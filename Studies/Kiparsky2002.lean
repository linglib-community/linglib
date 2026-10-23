module

public import Linglib.Core.Order.Interval.Basic

/-!
# Kiparsky (2002): Event Structure and the Perfect

This file formalizes [kiparsky-2002]'s account of the polysemy of the English perfect. The
readings of [1], with the recent past a special case of the resultative, are the possible
assignments of a verbal predicate's event structure to the temporal parameters E, R and P of the
[reichenbach-1947] schema of [2], in which the perfect's E precedes R, [4]: the existential
reading places the event in E, the universal reading makes it coextensive with E, the resultative
reading places the activity of a telic predicate in E and its change of state between E and R
with the result state holding through R, and the present state reading places R in the result
state and leaves the change of state implicit (`PerfectReading.mapping`). An event structure is
simple, a single run time, or complex, a run time with an activity and a result state
(`TemporalDecomposition`), so the two result-state readings need the complex decomposition of a
telic predicate (`isComplex_of_presentState`).

The three arguments for the polysemy rest on one structural contrast: under the existential and
universal readings the event precedes R (`precedes_of_existential`), under the resultative and
present state readings the result state, and with it the event, extends through R
(`le_runtime_of_presentState`), so no configuration is of both kinds. A subordinate perspective
time anchored to the main-clause event, [16], therefore precedes the main perspective time in the
first case and includes it in the second, which is why [declerck-1991]'s sequence of tense
contrast, [25], separates the existential and universal perfects from the resultative
(`sequenceOfTense_of_existential`, `no_sequenceOfTense_of_resultative`). Adverbs specify R, and
the present perfect's R includes P, so [klein-1992]'s puzzle dissolves: no adverb anterior to P
is possible, while the past perfect's two readings with such an adverb, [33], are the two sides
of the contrast (`present_perfect_puzzle`). And the resultative reading is the only one that
assigns the activity and the result state to different parameters, which is what lets the
activity be presupposed and the change of state asserted, the source of the Wh-puzzle of [39]
(`resultative_distinguishes`).

## Implementation notes

* E, R and P are intervals, [2], and precedence is the strict `NonemptyInterval.Precedes`, so
  the event of the universal reading ends before R; the inclusive boundaries remarked on for
  [10] are not represented.
* The anchoring rule [16a] is read at its tightest, the subordinate perspective time being the
  main-clause event's trace.

## References

* [kiparsky-2002]
* [reichenbach-1947]
* [declerck-1991]
* [klein-1992]
-/

@[expose] public section

namespace Kiparsky2002

open NonemptyInterval

variable {T : Type*} [LinearOrder T]

/-- The two phases of a telic event, an activity and the result state it leads to, the activity
ending no later than the result state begins. -/
structure SubeventPhases (T : Type*) [LinearOrder T] where
  activityTrace : NonemptyInterval T
  resultTrace : NonemptyInterval T
  activity_precedes_result : activityTrace.snd ≤ resultTrace.fst

/-- The event structure of a predicate is simple, a single run time, as for states and
activities, or complex, a run time containing an activity and a result state, as for
accomplishments and achievements. -/
inductive TemporalDecomposition (T : Type*) [LinearOrder T]
  | simple (runtime : NonemptyInterval T)
  | complex (runtime : NonemptyInterval T) (phases : SubeventPhases T)
      (activity_in_runtime : phases.activityTrace ≤ runtime)
      (result_in_runtime : phases.resultTrace ≤ runtime)

/-- The run time of an event structure. -/
def TemporalDecomposition.runtime : TemporalDecomposition T → NonemptyInterval T
  | .simple r => r
  | .complex r _ _ _ => r

/-- An event structure is complex when it has an activity and a result state. -/
def TemporalDecomposition.isComplex : TemporalDecomposition T → Prop
  | .simple _ => False
  | .complex _ _ _ _ => True

/-- The readings of the perfect, [1], the recent past being a special case of the resultative. -/
inductive PerfectReading
  | existential
  | universal
  | resultative
  | presentState
  deriving DecidableEq, Repr

/-- In the perfect's temporal schema, [4], the event interval E precedes the reference interval
R, and tense relates R to the perspective interval P. -/
structure Perfect (T : Type*) [LinearOrder T] where
  E : NonemptyInterval T
  R : NonemptyInterval T
  P : NonemptyInterval T
  perfect : E.Precedes R

namespace Perfect

variable (s : Perfect T)

/-- The present perfect, [3a], is the unmarked inclusion of P in R. -/
def Present : Prop := s.P ≤ s.R

/-- In the past perfect, [4], R precedes P. -/
def Past : Prop := s.R.Precedes s.P

end Perfect

/-- The assignment of event structure to the perfect's parameters under each reading, [6], [9],
[11] and [13]: the event in E; the event coextensive with E; the activity in E, the change of
state between E and R and R in the result state; R in the result state alone. -/
def PerfectReading.mapping (s : Perfect T) : PerfectReading → TemporalDecomposition T → Prop
  | .existential, d => d.runtime ≤ s.E
  | .universal, d => d.runtime = s.E
  | .resultative, .complex _ p _ _ =>
      p.activityTrace ≤ s.E ∧ s.E.snd ≤ p.resultTrace.fst ∧ s.R ≤ p.resultTrace
  | .presentState, .complex _ p _ _ => s.R ≤ p.resultTrace
  | .resultative, .simple _ | .presentState, .simple _ => False

open PerfectReading

variable {s : Perfect T} {d : TemporalDecomposition T}

/-! ### The readings -/

theorem existential_of_universal (h : universal.mapping s d) : existential.mapping s d :=
  le_of_eq h

theorem presentState_of_resultative (h : resultative.mapping s d) :
    presentState.mapping s d := by
  cases d with
  | simple _ => exact (h : False).elim
  | complex _ _ _ _ => obtain ⟨_, _, h⟩ := h; exact h

theorem isComplex_of_presentState (h : presentState.mapping s d) : d.isComplex := by
  cases d with
  | simple _ => exact (h : False).elim
  | complex _ _ _ _ => trivial

theorem precedes_of_existential (h : existential.mapping s d) : d.runtime.Precedes s.R :=
  lt_of_le_of_lt (NonemptyInterval.le_def.mp h).2 s.perfect

theorem le_runtime_of_presentState (h : presentState.mapping s d) : s.R ≤ d.runtime := by
  cases d with
  | simple _ => exact (h : False).elim
  | complex _ _ _ hr => exact le_trans h hr

/-- The readings are semantically distinct, §1, since no configuration is both existential and
a result-state one. -/
theorem not_existential_of_presentState (h : presentState.mapping s d) :
    ¬ existential.mapping s d :=
  λ he => precedes_not_overlaps (precedes_of_existential he)
    (overlaps_symm (overlaps_of_le (le_runtime_of_presentState h)))

/-! ### The sequence of tense puzzle, §2 -/

theorem sequenceOfTense_of_existential (h : existential.mapping s d)
    (hRP : s.R.fst ≤ s.P.fst) : d.runtime.Precedes s.P :=
  lt_of_lt_of_le (precedes_of_existential h) hRP

theorem no_sequenceOfTense_of_resultative (h : resultative.mapping s d) (hP : s.Present) :
    s.P ≤ d.runtime ∧ ¬ d.runtime.Precedes s.P :=
  have hPd : s.P ≤ d.runtime :=
    le_trans hP (le_runtime_of_presentState (presentState_of_resultative h))
  ⟨hPd, λ hlt => precedes_not_overlaps hlt (overlaps_symm (overlaps_of_le hPd))⟩

/-! ### The present perfect puzzle, §3 -/

theorem present_perfect_puzzle (hP : s.Present) : ¬ s.Past :=
  λ hpast => precedes_not_overlaps hpast (overlaps_symm (overlaps_of_le hP))

/-! ### The Wh-puzzle, §4 -/

variable {rt : NonemptyInterval T} {p : SubeventPhases T} {ha : p.activityTrace ≤ rt}
  {hr : p.resultTrace ≤ rt}

theorem phases_le_of_existential (h : existential.mapping s (.complex rt p ha hr)) :
    p.activityTrace ≤ s.E ∧ p.resultTrace ≤ s.E :=
  ⟨le_trans ha h, le_trans hr h⟩

theorem resultative_distinguishes (h : resultative.mapping s (.complex rt p ha hr)) :
    p.activityTrace ≤ s.E ∧ ¬ p.resultTrace ≤ s.E :=
  have ⟨h₁, _, h₃⟩ := h
  ⟨h₁, λ hle => precedes_not_overlaps s.perfect
    (overlaps_symm (overlaps_of_le (le_trans h₃ hle)))⟩

end Kiparsky2002
