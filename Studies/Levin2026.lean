module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.ArgumentStructure.LevinClass.Members
public import Linglib.Semantics.ArgumentStructure.LevinClass.Properties
public import Linglib.Fragments.English.Adjectives
public import Linglib.Data.Examples.Levin2026

/-!
# Levin (2026): The door pushed open

This file formalizes Levin's analysis of the English intransitive resultative with
transitive-only verbs, *The door pushed open*, *The cork pulled free*, *The valve slammed
shut*. Outside the resultative these verbs have no intransitive use whose subject is their
object, *The door pushed*. Levin takes the intransitive resultative to be the anticausative
variant of the causative alternation and its transitive counterpart the causative variant. The
resultative describes a change of state that the verb alone does not, which is what makes the
alternation available, and the conditions on the anticausative variant decide when the cause
may go unexpressed.

The verbs are verbs of exerting force and verbs of surface contact, manner verbs that do not
lexicalize a change (`VerbKind`). The result adjectives are *open*, *closed*, *shut*, *free*,
*loose* and *flat* in the sense that describes a spatial configuration with respect to a
reference entity, and not in their other senses, *free of shards*. The subject must be able to
move without the continuous involvement of a cause, as an animate, a machine or a projectile
can (`Theme.SelfEnergetic`), since a change of state properly contained in the causing act
requires the cause to be expressed, the Proper Containment Condition of Rappaport Hovav and
Levin (`CauseRequired`). Neither the verb nor the adjective suffices alone, and a sentence of
the paper is acceptable exactly when the three conditions meet or the verb alternates by
itself (`acceptable_iff_licensed`). Neo-constructional approaches, on which a verb's lexical
properties do not constrain its distribution, expect every verb in every resultative pattern, and
must explain why such intransitive resultatives are not more pervasive: *The tub scrubbed clean*
is unacceptable (footnote 7, (16); `exists_unacceptable_intransitive_resultative`).

## Implementation notes

The verb classes are the paper's own lists, not the classes of Levin's 1993 book, from which
they differ, *fling* being there a verb of throwing, as the paper notes
(`exertingForce_not_all_pushPull`). The discourse conditions on the anticausative
variant, a cause recoverable from the context or of unknown identity, are conditions of use
that no judgment of the paper isolates, and are not modelled; nor are the two intransitive
resultatives with other adjectives that the paper offers as possible one-off instances. The
kind of the subject is recorded for the rows whose subject the paper discusses.

## References

* [levin-2026]
* [rappaport-hovav-levin-2012]
* [rappaport-hovav-2014]
* [levin-1993]
-/

@[expose] public section

namespace Levin2026

open ArgumentStructure

/-! ### The proper containment condition -/

section ProperContainment

variable {T : Type*} [LinearOrder T] {act change : NonemptyInterval T}

/-- The cause must be expressed when the change of state is properly contained within the
causing act. -/
def CauseRequired (act change : NonemptyInterval T) : Prop := change < act

theorem not_causeRequired_of_outlasts (h : act.snd < change.snd) :
    ¬ CauseRequired act change :=
  fun hlt ↦ absurd (NonemptyInterval.le_def.1 hlt.le).2 h.not_ge

end ProperContainment

/-! ### Verbs, adjectives and subjects -/

/-- The verbs of the paper's examples are the verbs of exerting force, the two subtypes of verbs
of surface contact, the verbs of change of state, which show the causative alternation by
themselves, and the other verbs, which are outside the paper's lists. -/
inductive VerbKind
  | exertingForce
  | hitting
  | wiping
  | changeOfState
  | other
  deriving DecidableEq, Repr

/-- A verb of exerting force or of surface contact describes the application of a force to an
entity. -/
def VerbKind.AppliesForce (k : VerbKind) : Prop :=
  k = .exertingForce ∨ k = .hitting ∨ k = .wiping

instance : DecidablePred VerbKind.AppliesForce := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A verb of surface contact describes an entity coming into contact with another through the
imparting of a force. -/
def VerbKind.IsSurfaceContact (k : VerbKind) : Prop := k = .hitting ∨ k = .wiping

instance : DecidablePred VerbKind.IsSurfaceContact :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The attested verbs of exerting force. -/
def exertingForceVerbs : List String :=
  ["fling", "jerk", "pull", "push", "shove", "tug", "wrench", "yank"]

/-- The attested verbs of hitting. -/
def hittingVerbs : List String := ["bang", "kick", "punch", "slam", "smack", "thrash", "thump"]

/-- The attested verbs of wiping, with *wipe* itself. -/
def wipingVerbs : List String := ["scrape", "sweep", "wipe"]

/-- The verbs by their `paperFeatures` labels. -/
def VerbKind.labels : List (String × VerbKind) :=
  exertingForceVerbs.map (·, .exertingForce) ++ hittingVerbs.map (·, .hitting) ++
    wipingVerbs.map (·, .wiping) ++ [("freeze", .changeOfState)] ++
    ["scrub", "cut", "sew", "brush", "pat", "paint", "wire", "shovel", "lever", "nudge", "oil",
      "nail"].map (·, .other)

/-- A result adjective is used in its spatially instantiated sense or in another. -/
inductive Sense
  | spatial
  | other
  deriving DecidableEq, Repr

/-- The senses by their `paperFeatures` labels. -/
def Sense.labels : List (String × Sense) := [("spatial", .spatial), ("other", .other)]

/-- The result adjectives by their `paperFeatures` labels, with the fragment entry of those the
fragment has. -/
def adjectiveLabels : List (String × Option Degree.GradableAdjective) :=
  open English.Adjectives in
  [("open", some open_), ("closed", some closed_), ("shut", some shut), ("free", some free_),
   ("loose", some loose), ("flat", some flat), ("solid", none), ("clean", none), ("bald", none),
   ("firm", none), ("smooth", none), ("senseless", none)]

/-- The kinds of entity a subject denotes. -/
inductive Theme
  | animate
  | machine
  | projectile
  | naturalForce
  | manipulated
  deriving DecidableEq, Repr

/-- A self-energetic entity moves without the continuous involvement of an external cause;
an entity that an agent manipulates throughout the event does not. -/
def Theme.SelfEnergetic (t : Theme) : Prop := t ≠ .manipulated

instance : DecidablePred Theme.SelfEnergetic := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The kinds of subject by their `paperFeatures` labels. -/
def Theme.labels : List (String × Theme) :=
  [("animate", .animate), ("machine", .machine), ("projectile", .projectile),
   ("natural force", .naturalForce), ("manipulated", .manipulated)]

/-- The frames of the paper's examples. -/
inductive Frame
  | transitive
  | intransitive
  | directedMotion
  deriving DecidableEq, Repr

/-- The frames by their `paperFeatures` labels. -/
def Frame.labels : List (String × Frame) :=
  [("transitive", .transitive), ("intransitive", .intransitive),
   ("directed motion", .directedMotion)]

/-! ### Licensing -/

/-- A result phrase has an adjective, recorded where the fragment has it, and the sense the
adjective is used in. -/
structure Result where
  adjective : Option Degree.GradableAdjective
  sense : Sense

/-- A result phrase describes a spatially instantiated state when its adjective has a spatial
configuration and is used in that sense. -/
def Result.IsSpatial (r : Result) : Prop :=
  r.sense = .spatial ∧ ∃ a ∈ r.adjective, a.spatialConfigType.isSome

instance : DecidablePred Result.IsSpatial := fun r ↦
  inferInstanceAs (Decidable (r.sense = .spatial ∧ ∃ a ∈ r.adjective, a.spatialConfigType.isSome))

/-- An example of the paper records the kind of its verb, its result phrase and the kind of its
subject, where it has them, its frame and its judgment. -/
structure Row where
  verb : VerbKind
  result : Option Result
  theme : Option Theme
  frame : Frame
  judgment : Judgment

/-- An intransitive whose subject is the verb's object is licensed when the verb is a verb of
change of state, or when a verb that applies a force combines with a spatially instantiated
result predicated of a self-energetic subject. -/
def Row.Licensed (d : Row) : Prop :=
  d.verb = .changeOfState ∨
    (d.verb.AppliesForce ∧ (∃ r ∈ d.result, r.IsSpatial) ∧ ∃ t ∈ d.theme, t.SelfEnergetic)

instance : DecidablePred Row.Licensed := fun d ↦
  inferInstanceAs (Decidable (d.verb = .changeOfState ∨
    (d.verb.AppliesForce ∧ (∃ r ∈ d.result, r.IsSpatial) ∧ ∃ t ∈ d.theme, t.SelfEnergetic)))

/-- An optional feature of an example, read through a table. -/
def optional? {α : Type*} (e : Datum) (key : String) (table : List (String × α)) :
    Option (Option α) :=
  match e.feature? key with
  | none => some none
  | some v => (table.lookup v).map some

/-- The result phrase of an example, none when the row names no adjective. -/
def result? (e : Datum) : Option (Option Result) :=
  match e.feature? "adjective" with
  | none => some none
  | some _ => do
    pure (some { adjective := ← e.parse? "adjective" adjectiveLabels
                 sense := ← e.parse? "sense" Sense.labels })

/-- A datum read into its row. -/
def Row.ofDatum (e : Datum) : Option Row := do
  pure { verb := ← e.parse? "verb" VerbKind.labels
         result := ← result? e
         theme := ← optional? e "theme" Theme.labels
         frame := ← e.parse? "frame" Frame.labels
         judgment := e.judgment }

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (Row.ofDatum e).isSome := by decide +kernel

/-- The paper's examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

theorem acceptable_iff_licensed :
    ∀ d ∈ data, d.frame = .intransitive → (d.judgment = .acceptable ↔ d.Licensed) := by
  decide +kernel

theorem exists_unacceptable_appliesForce :
    (∃ d ∈ data, d.verb.AppliesForce ∧ d.frame = .intransitive ∧ d.result = none ∧
      d.judgment ≠ .acceptable) ∧
    ∃ d ∈ data, d.verb.AppliesForce ∧ d.frame = .intransitive ∧ d.result.isSome ∧
      d.judgment ≠ .acceptable := by
  decide +kernel

theorem exists_unacceptable_spatial :
    ∃ d ∈ data, d.frame = .intransitive ∧ (∃ r ∈ d.result, r.IsSpatial) ∧
      d.judgment ≠ .acceptable := by
  decide +kernel

theorem causative_variants :
    ∀ k ∈ [VerbKind.exertingForce, .hitting],
      (∃ d ∈ data, d.verb = k ∧ d.frame = .transitive ∧ d.result.isSome ∧
        d.judgment = .acceptable) ∧
      ∃ d ∈ data, d.verb = k ∧ d.frame = .intransitive ∧ d.result.isSome ∧
        d.judgment = .acceptable := by
  decide +kernel

theorem directedMotion_selfEnergetic :
    ∀ d ∈ data, d.frame = .directedMotion →
      d.verb.IsSurfaceContact ∧ ∃ t ∈ d.theme, t.SelfEnergetic := by
  decide +kernel

theorem not_licensed_of_manipulated {d : Row} (hv : d.verb ≠ .changeOfState)
    (ht : d.theme = some .manipulated) : ¬ d.Licensed := by
  rintro (h | ⟨-, -, t, ht', hs⟩)
  · exact hv h
  · rw [ht] at ht'
    exact hs (Option.some.inj ht').symm

/-! ### The construction does not restrict the alternation -/

theorem participates_causativeInchoative :
    ¬ LevinClass.pushPull.Participates .causativeInchoative ∧
    ¬ LevinClass.hit.Participates .causativeInchoative ∧
    LevinClass.otherChangeOfState.Participates .causativeInchoative := by
  decide

theorem exertingForce_not_all_pushPull :
    ∃ v ∈ exertingForceVerbs, "fling" = v ∧ v ∉ LevinClass.members .pushPull ∧
      v ∈ LevinClass.members .throw := by
  decide +kernel

/-- Neo-constructional approaches "do not take a verb's lexical properties to constrain its
distribution, so any verb would be expected to appear in all resultative patterns" (footnote 7),
but a verb outside the paper's lists is unacceptable in the intransitive resultative, as in (16d)
*The tub scrubbed clean*. -/
theorem exists_unacceptable_intransitive_resultative :
    ∃ d ∈ data, d.verb = .other ∧ d.frame = .intransitive ∧ d.result.isSome ∧
      d.judgment ≠ .acceptable := by
  decide +kernel

end Levin2026
