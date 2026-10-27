module

public import Linglib.Core.Probability.UniformOn
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Semantics.Aspect.Phasal
public import Linglib.Semantics.Presupposition.Context
public import Linglib.Semantics.Questions.Resolution

/-!
# Roberts and Simons (2024): Preconditions and Projection: Explaining Non-Anaphoric Presupposition

Roberts and Simons explain the projective content of change-of-state predicates, factives and
selectional restrictions without a lexical constraint on the context. That content describes the
ontological preconditions of the event type the predicate denotes, the conditions any event of
the type depends on, so a sentence describing the event entails them. Projection is the
listener's inference that the speaker presumes a context entailing them, as in the models of
Qing, Goodman and Lassiter and of Warstadt. A negated trigger is more informative relative to a
context restricted to the precondition, and a precondition, unlike a consequence of the event,
can hold where the event does not, so it is the safe thing to accommodate. Projection is
suppressed where the presumption cannot be attributed to the speaker, and filtering is the case
in which the speaker has asserted, supposed or entertained the precondition, so that the trigger
is evaluated in a context that includes it.

## Main statements

* `cosOccurs_subset_cosPrecondition`: a change of state entails its precondition.
* `mem_cosPrecondition_diff_cosOccurs`, `inter_compl_cosOccurs_eq_empty`: a precondition is
  consistent with the negated trigger, and an entailment holding only where the change occurs is
  not.
* `uniformOn_raining_compl_knows`: restricting the context to the precondition makes the negative
  answer less probable, so more informative.
* `localContext_subset`: a trigger is filtered where its local context entails the precondition.

## Implementation notes

Indices are world–time pairs. A change of state occurs where the meaning of the phasal verb,
`Aspect.Phasal.denote`, is defined and true, and its precondition is the presupposition of that
meaning, the prior state at an earlier index, so that its occurrence entails its precondition.
The paper's two diagnostics for preconditions, the "part of what allowed for" frame and the
counterfactual, sort entailments into preconditions, consequences and concomitants ontologically
rather than semantically, so they are not derived here. The cells of the question about Jane are
equiprobable, the paper's "roughly equal" probabilities.

## TODO

* The paper's (28) is Karttunen's contrast between *discover* and *regret*
  (`Karttunen1971b.projection_rows`). Only the conditional (28c) is derived here, not the
  question (28b) or the projection of *regret*.
* The reference-time account of the contrast between *know* and *discover* in (32)–(34).

## References

* [C. Roberts, M. Simons, *Preconditions and Projection: Explaining Non-Anaphoric Presupposition*
  (2024)][roberts-simons-2024]
* [L. Karttunen, *Some observations on factivity* (1971)][karttunen-1971b]
* [L. Karttunen, *Presuppositions of Compound Sentences* (1973)][karttunen-1973]
* [R. C. Stalnaker, *Pragmatic Presuppositions* (1974)][stalnaker-1974]
* [L. Karttunen, *Presupposition and Linguistic Context* (1974)][karttunen-1974-presupposition]
* [I. Heim, *On the Projection Problem for Presuppositions* (1983)][heim-1983]
* [C. Qing, N. D. Goodman, D. Lassiter, *A Rational Speech-Act Model of Projective Content*
  (2016)][qing-goodman-lassiter-2016]
* [A. Warstadt, *Presupposition Triggering Reflects Pragmatic Reasoning about Utterance Utility*
  (2022)][warstadt-2022]
-/

@[expose] public section

namespace RobertsSimons2024

open Aspect Question MeasureTheory ProbabilityTheory
open scoped SetRel

variable {ι : Type*}

/-! ### Ontological preconditions (§2) -/

section ChangeOfState

variable (t : Phasal) (R : SetRel ι ι) (P : ι → Prop)

/-- A change of state occurs at an index when the prior state held at an earlier index and the
result state holds at the index, which is where the phasal verb is defined and true. -/
def cosOccurs : Set ι := posSupport (t.denote R P)

/-- The ontological precondition of a change of state is its prior state at an earlier index, as
being on the ladder is for falling off it (5). It is what the phasal verb presupposes. -/
def cosPrecondition : Set ι := Function.support (t.denote R P)

variable {t R P}

/-- A sentence describing a change of state entails its precondition (§2.1). -/
theorem cosOccurs_subset_cosPrecondition : cosOccurs t R P ⊆ cosPrecondition t R P :=
  fun _ h ↦ ne_of_eq_of_ne h one_ne_zero

/-! ### Why preconditions project (§3.1) -/

/-- The precondition of a change of state can hold without the change, so accommodating it is
consistent with *John didn't stop smoking* (§3.1). -/
theorem mem_cosPrecondition_diff_cosOccurs {i i' : ι} (hr : i ~[R] i') (hp : t.Prior (P i'))
    (hn : ¬ t.Result (P i)) : i ∈ cosPrecondition t R P \ cosOccurs t R P :=
  ⟨Phasal.denote_eq_zero_iff.not_left.2 ⟨i', hr, hp⟩, by simp [cosOccurs, Phasal.denote, hn]⟩

/-- An entailment holding only where the change occurs is inconsistent with the negated trigger
(§3.1). -/
theorem inter_compl_cosOccurs_eq_empty {F : Set ι} (hF : F ⊆ cosOccurs t R P) :
    F ∩ (cosOccurs t R P)ᶜ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨h, hn⟩ ↦ hn (hF h)

/-- In *John didn't stop smoking*, with the Fragment's *stop*, John's having smoked is consistent
with the negated trigger (§3.1). -/
theorem stop_mem_cosPrecondition_diff_cosOccurs {i i' : ι} (hr : i ~[R] i') (h' : P i')
    (h : P i) :
    ∃ t, English.Verbs.stop.phasal = some t ∧ i ∈ cosPrecondition t R P \ cosOccurs t R P :=
  ⟨.cessation, rfl, mem_cosPrecondition_diff_cosOccurs hr h' (not_not_intro h)⟩

end ChangeOfState

/-- The cells of the question "Does Jane know that it's raining?" in the §3.1 diagram are
raining and Jane knows it, raining and she doesn't, and not raining. -/
inductive Cell
  | rainKnown
  | rainUnknown
  | noRain
  deriving DecidableEq, Fintype

instance : MeasurableSpace Cell := ⊤
instance : DiscreteMeasurableSpace Cell := ⟨fun _ ↦ trivial⟩

/-- R, that it's raining. -/
def raining : Set Cell := {.rainKnown, .rainUnknown}

/-- K(j,r), that Jane knows that it's raining. -/
def knows : Set Cell := {.rainKnown}

private theorem ncard_raining : raining.ncard = 2 := Set.ncard_pair nofun

private theorem ncard_univ_cell : (Set.univ : Set Cell).ncard = 3 := by
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]; rfl

/-- Restricting the context to raining makes *Jane doesn't know that it's raining* less probable and
as probable as its positive answer (§3.1). -/
theorem uniformOn_raining_compl_knows :
    (uniformOn raining).real knowsᶜ < (uniformOn Set.univ).real knowsᶜ ∧
      (uniformOn raining).real knowsᶜ = (uniformOn raining).real knows := by
  have h₁ : raining ∩ knowsᶜ = {.rainUnknown} := by ext x; cases x <;> simp [raining, knows]
  have h₂ : raining ∩ knows = {.rainKnown} := by ext x; cases x <;> simp [raining, knows]
  have h₃ : Set.univ ∩ knowsᶜ = {.rainUnknown, .noRain} := by ext x; cases x <;> simp [knows]
  simp only [uniformOn_real_apply, h₁, h₂, h₃, ncard_raining, ncard_univ_cell,
    Set.ncard_singleton, Set.ncard_pair (show Cell.rainUnknown ≠ .noRain from nofun)]
  norm_num

/-- The affirmative *Jane knows that it's raining* is informative relative to either context
(§3.1). -/
theorem uniformOn_knows_lt_one :
    (uniformOn Set.univ).real knows < 1 ∧ (uniformOn raining).real knows < 1 := by
  have h₁ : Set.univ ∩ knows = {.rainKnown} := Set.univ_inter _
  have h₂ : raining ∩ knows = {.rainKnown} := by ext x; cases x <;> simp [raining, knows]
  simp only [uniformOn_real_apply, h₁, h₂, ncard_raining, ncard_univ_cell, Set.ncard_singleton]
  norm_num

/-! ### Suppression (§3.2)

On the projective reading the speaker presumes a context `C` entailing the precondition `pre` of
the event they raise, `C ⊆ pre` (§3.1); suppression is the case in which that presumption cannot
be attributed to them. -/

/-- Projection is suppressed when someone who must accept the presumed context doubts the
precondition, as in (23) and (24) (cases 1 and 2 of §3.2.1). -/
theorem not_presumes_of_doubt {C S pre : Set ι} (hS : S ⊆ C) (h : ¬ S ⊆ pre) : ¬ C ⊆ pre :=
  fun hp ↦ h (hS.trans hp)

/-- Presuming a precondition that is an alternative of the question under discussion resolves it, so
projection is suppressed in (25) (case 3 of §3.2.1). -/
theorem resolves_of_presumes {C pre : Set ι} {Q : Question ι} (h : pre ∈ alt Q) (hp : C ⊆ pre) :
    C ∈ Q :=
  mem_of_exists_alt_subset ⟨_, h, hp⟩

/-- A speaker who presumes she is ignorant whether `P` cannot presume `P` ((28c), (29), after
[stalnaker-1974]). -/
theorem not_subset_of_presumes_ignorance {Dox : ι → Set ι} {C P : Set ι} {w : ι} (hw : w ∈ C)
    (hbel : Dox w ⊆ C) (hign : C ⊆ {v | ¬ Dox v ⊆ P}) : ¬ C ⊆ P :=
  fun hP ↦ hign hw (hbel.trans hP)

/-! ### Filtering (§4)

The filtering constructions (41), (42), (43) place the trigger in the second conjunct, in the
consequent, or in a disjunct. The paper shares with the satisfaction theory the assumption that
the trigger is evaluated in the context updated with the other clause, the local context of
[karttunen-1974-presupposition]'s table (`Presupposition.Connective.localContext`), but not the
requirement that the local context entail the precondition. -/

open Presupposition (Connective)

/-- The local context entails the precondition when the first conjunct or antecedent does, or when
the other disjunct's negation does (§4). -/
theorem localContext_subset {C A pre : Set ι} :
    (A ⊆ pre → Connective.conj.localContext C A ⊆ pre ∧ Connective.cond.localContext C A ⊆ pre) ∧
      (Aᶜ ⊆ pre → Connective.disj.localContext C A ⊆ pre) :=
  ⟨fun h ↦ ⟨fun _ hw ↦ h hw.2, fun _ hw ↦ h hw.2⟩, fun h _ hw ↦ h hw.2⟩

/-- In a context leaving the precondition open, a disjunctive antecedent whose other disjunct
negates it filters it, and a simple antecedent does not (44). -/
theorem disjunctive_antecedent_filters {C pre : Set ι} (hopen : ¬ C ⊆ pre) :
    Connective.disj.localContext C preᶜ ⊆ pre ∧ ¬ Connective.cond.localContext C Set.univ ⊆ pre :=
  ⟨fun _ hw ↦ not_not.mp hw.2, fun h ↦ hopen fun _ hw ↦ h ⟨hw, trivial⟩⟩

end RobertsSimons2024
