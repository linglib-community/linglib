module

public import Linglib.Data.Experiments.DegenTonhauser2022
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Verbs.Copular
public import Linglib.Semantics.Presupposition.Verb
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Degen and Tonhauser (2022): Are there factive predicates? An empirical investigation

A clause-embedding predicate is factive, on Kiparsky and Kiparsky's definition, when the content
of its complement is presupposed, and on Gazdar's when that content is presupposed and entailed.
Degen and Tonhauser test both definitions on twenty English predicates, diagnosing presupposition
by projection and entailment by inference and by contradictoriness, each under a gradient and a
categorical response task. On the first definition the canonically factive predicates should
project categorically more than the rest, and they do not: the optionally factive *acknowledge*,
*hear* and *inform* project at least as much as *reveal*. On the second, every complement
projects, so the factive predicates are those with entailed complements, and under every
diagnostic and task these are none, or not categorically more projective than the rest.

## Main statements

* `not_exists_threshold`: no threshold on the certainty ratings picks out the canonically factive
  predicates, under either task.
* `factive_eq_empty_or_not_separates`: the predicates whose complement is both projective and
  entailed are none, or not categorically more projective than the rest.
* `isFactive_iff`: the predicates the English lexicon marks factive are the canonically factive
  ones.

## Implementation notes

* A class is categorically more projective when every member's mean certainty rating exceeds
  every non-member's, `Separates`; over finitely many predicates this is a threshold on the
  ratings.
* Projective and entailed are the paper's verdicts from its regressions: a complement projects
  when its ratings are distinguished from the main-clause controls', and is entailed when they
  are not distinguished from those of the controls with entailed content.

## References

* [degen-tonhauser-2022]
* [kiparsky-kiparsky-1970]
* [gazdar-1979]
-/

@[expose] public section

namespace DegenTonhauser2022

open Set

/-! ### The predicates in the lexicon -/

section Fragment

open English
open English.Verbs hiding Verb
open English.Verbs.Copular

/-- The English lexical entry of a predicate. -/
def entry : Predicate → Verb
  | .acknowledge => acknowledge.toVerb
  | .admit => admit.toVerb
  | .announce => announce.toVerb
  | .beAnnoyed => beAnnoyed
  | .beRight => beRight
  | .confess => confess.toVerb
  | .confirm => confirm.toVerb
  | .demonstrate => demonstrate.toVerb
  | .discover => discover.toVerb
  | .establish => establish.toVerb
  | .hear => hear.toVerb
  | .inform => inform.toVerb
  | .know => know.toVerb
  | .pretend => pretend.toVerb
  | .prove => prove.toVerb
  | .reveal => reveal.toVerb
  | .say => say.toVerb
  | .see => see.toVerb
  | .suggest => suggest.toVerb
  | .think => think.toVerb

end Fragment

/-- The predicates of a category of the paper's classification. -/
def Category.predicates (c : Category) : Set Predicate := {p | p ∈ (classification c).predicates}

instance (c : Category) : DecidablePred (· ∈ c.predicates) :=
  fun p ↦ inferInstanceAs (Decidable (p ∈ (classification c).predicates))

/-- The English lexicon marks factive exactly the canonically factive predicates. -/
theorem isFactive_iff {p : Predicate} :
    (entry p).IsFactive ↔ p ∈ Category.canonicallyFactive.predicates := by
  cases p <;> decide

theorem isTrigger_iff {p : Predicate} : (entry p).IsTrigger ↔ (entry p).IsFactive := by
  cases p <;> decide

/-! ### Categorical distinctions -/

section Separates

variable {α β : Type*} [LinearOrder β] {s : Set α} {f : α → β} {a b : α}

/-- A rating separates a class when it rates every member above every non-member. -/
def Separates (s : Set α) (f : α → β) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∉ s → f b < f a

theorem not_separates_of_le (ha : a ∈ s) (hb : b ∉ s) (h : f a ≤ f b) : ¬ Separates s f :=
  fun hs ↦ (hs ha hb).not_ge h

theorem separates_iff_exists_threshold [Finite α] (h : sᶜ.Nonempty) :
    Separates s f ↔ ∃ t, s = f ⁻¹' Ioi t := by
  obtain ⟨b, hb, hmax⟩ := sᶜ.exists_max_image f sᶜ.toFinite h
  refine ⟨fun hs ↦ ⟨f b, ext fun a ↦ ?_⟩, ?_⟩ <;> grind [Separates]

end Separates

/-! ### Factive as presupposed -/

/-- The mean certainty rating of a predicate's complement under a task. -/
def certaintyMean (t : Task) (p : Predicate) : ℚ := (certainty t p).mean.toRat

/-- A predicate's complement projects under a task when its certainty ratings are distinguished
from the main-clause controls'. -/
def Projects (t : Task) (p : Predicate) : Prop := p ∉ (projectionResults t).indistinguishable

instance (t : Task) : DecidablePred (Projects t) := fun _ ↦ inferInstanceAs (Decidable (_ ∉ _))

theorem projects (t : Task) (p : Predicate) : Projects t p := by
  cases t <;> exact List.not_mem_nil

theorem certaintyMean_reveal_le_iff (t : Task) (p : Predicate) :
    certaintyMean t .reveal ≤ certaintyMean t p ↔
      p ∈ Category.canonicallyFactive.predicates ∨ p ∈ [.acknowledge, .hear, .inform] := by
  revert t p; decide +kernel

theorem certaintyMean_lt_of_mem_of_not_mem {t : Task} {p q : Predicate}
    (hp : p ∈ Category.canonicallyFactive.predicates)
    (hq : q ∉ Category.canonicallyFactive.predicates) (hq' : q ∉ [.acknowledge, .hear, .inform]) :
    certaintyMean t q < certaintyMean t p :=
  (not_le.1 fun h ↦ ((certaintyMean_reveal_le_iff t q).1 h).elim hq hq').trans_le
    ((certaintyMean_reveal_le_iff t p).2 (.inl hp))

theorem not_separates_certaintyMean (t : Task) :
    ¬ Separates Category.canonicallyFactive.predicates (certaintyMean t) :=
  not_separates_of_le (a := .reveal) (b := .inform) (by decide) (by decide)
    ((certaintyMean_reveal_le_iff t _).2 (.inr (by decide)))

/-- No threshold on either task's certainty ratings picks out the canonically factive
predicates. -/
theorem not_exists_threshold (t : Task) :
    ¬ ∃ θ, Category.canonicallyFactive.predicates = certaintyMean t ⁻¹' Ioi θ :=
  (separates_iff_exists_threshold ⟨.inform, by decide⟩).not.1 (not_separates_certaintyMean t)

/-! ### Factive as presupposed and entailed -/

/-- A predicate's complement is entailed under a diagnostic and task when its ratings are not
distinguished from those of the controls with entailed content. -/
def Entailed (d : Diagnostic) (t : Task) (p : Predicate) : Prop :=
  p ∈ (entailmentResults d t).indistinguishable

instance (d : Diagnostic) (t : Task) : DecidablePred (Entailed d t) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- Under either diagnostic and task, no complement is projective and entailed, or the entailed
complement of *be right* projects less than the nonentailed one of *say*. -/
theorem factive_eq_empty_or_not_separates (d : Diagnostic) (t t' : Task) :
    {p | Projects t' p ∧ Entailed d t p} = ∅ ∨
      ¬ Separates {p | Projects t' p ∧ Entailed d t p} (certaintyMean t') := by
  simp only [projects, true_and]
  cases d
  · refine .inr (not_separates_of_le (a := .beRight) (b := .say) ?_ ?_ ?_) <;>
      revert t t' <;> decide +kernel
  · exact .inl (eq_empty_of_forall_notMem fun p ↦ by cases t <;> exact List.not_mem_nil)

theorem certaintyMean_lt_of_entailed {t : Task} {p q : Predicate}
    (hp : Entailed .inference .gradient p) (hq : q ∈ Category.canonicallyFactive.predicates) :
    certaintyMean t p < certaintyMean t q := by
  have : ∀ t p q, Entailed .inference .gradient p → q ∈ Category.canonicallyFactive.predicates →
      certaintyMean t p < certaintyMean t q := by decide +kernel
  exact this t p q hp hq

end DegenTonhauser2022
