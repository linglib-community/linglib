module

public import Linglib.Semantics.Events.Basic
public import Linglib.Logic.Trivalent.Pointwise

/-!
# Koev (2017): Evidentiality, Learning Events and Spatiotemporal Distance

Koev analyzes the Bulgarian evidential *-l* as spatiotemporal distance rather than a semantic
primitive. An evidential sentence introduces a learning event, through which the speaker
acquired the evidence for the claim, and requires it to be spatiotemporally distant from the
described event: either not overlapping it in time, as with standard indirect evidence, or
located elsewhere, as when smoke from a chimney shows a fire in progress. Direct witness, at the
same time and place, is the one configuration the evidential excludes, and the constraint is
independent of the ordering that past tense contributes. The evidential implication projects as
the presupposition of a trivalent proposition whose assertion is the core proposition, with no
modal weakening, against Izvorski.

## Main definitions

* `spatiotemporallyDistant`: the distance condition.
* `LearningScenario.toEvidentialProp`: the evidential sentence as a trivalent proposition.

## Implementation notes

* Events carry no location, so the distance predicate takes a location function as a
  parameter.
* The learning predicate itself, the knowledge change it reports, and the evidence-source
  typology of §5 are not modelled; the scenarios record only the two events.

## References

* [koev-2017]
* [izvorski-1997]
-/

@[expose] public section

namespace Koev2017

open Event (τ)

variable {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T] {L : Type*}

/-- Two events are temporally disjoint when their temporal traces do not overlap, the first
disjunct of Definition 24. -/
def temporallyDisjoint (e₁ e₂ : E) : Prop := ¬ (τ e₁).Overlaps (τ e₂)

/-- Two events are spatiotemporally distant, Definition 24, when they do not overlap in time or
occur at different locations. -/
def spatiotemporallyDistant (loc : E → L) (e₁ e₂ : E) : Prop :=
  temporallyDisjoint e₁ e₂ ∨ loc e₁ ≠ loc e₂

instance [DecidableEq T] (e₁ e₂ : E) : Decidable (temporallyDisjoint e₁ e₂) :=
  inferInstanceAs (Decidable (¬ (τ e₁).Overlaps (τ e₂)))

instance [DecidableEq T] [DecidableEq L] (loc : E → L) (e₁ e₂ : E) :
    Decidable (spatiotemporallyDistant loc e₁ e₂) :=
  inferInstanceAs (Decidable (temporallyDisjoint e₁ e₂ ∨ loc e₁ ≠ loc e₂))

theorem temporallyDisjoint_of_precedes {e₁ e₂ : E} (h : (τ e₁).Precedes (τ e₂)) :
    temporallyDisjoint e₁ e₂ :=
  NonemptyInterval.Precedes.not_overlaps h

/-- A learning scenario pairs the described event with the learning event through which the
speaker acquired the evidence for the claim, (74b). -/
structure LearningScenario (E : Type*) where
  /-- The described event. -/
  described : E
  /-- The learning event. -/
  learning : E

open Classical in
/-- The evidential sentence is a trivalent proposition whose presupposition is the distance
condition of the learning event, which restricts the context set, (74b), and whose assertion
is the core proposition, to which the declarative operator (72) commits the speaker. -/
noncomputable def LearningScenario.toEvidentialProp (loc : E → L) (s : LearningScenario E)
    {W : Type*} (p : W → Prop) : W → SignType :=
  {_w | spatiotemporallyDistant loc s.described s.learning}.indicator fun w ↦
    SignType.ofProp (p w)

/-- Negation preserves the evidential presupposition while negating the core proposition,
(78). -/
theorem projection_past_negation (loc : E → L) (s : LearningScenario E) {W : Type*}
    (p : W → Prop) :
    Function.support (-s.toEvidentialProp loc p) = Function.support (s.toEvidentialProp loc p) := by
  ext; simp

/-! ### The scenarios of §4 -/

/-- A `Place` locates the events of the scenarios. -/
inductive Place
  | here
  | there
  deriving DecidableEq, Repr

/-- The events of the scenarios are the described event and the learning events of standard
indirect evidence, of direct witness, and of seeing smoke from the chimney. -/
inductive Ev
  | described
  | learnIndirect
  | learnDirect
  | learnSmoke
  deriving DecidableEq, Repr

/-- The described event runs over `[0, 5]`; the speaker learns of it afterwards, witnesses it
during `[2, 4]`, or sees the smoke over the same interval `[0, 5]`. -/
instance : Event.TemporalTrace Ev ℤ where
  τ
    | .described => ⟨(0, 5), by decide⟩
    | .learnIndirect => ⟨(10, 15), by decide⟩
    | .learnDirect => ⟨(2, 4), by decide⟩
    | .learnSmoke => ⟨(0, 5), by decide⟩

/-- In standard indirect evidence, (25a), the speaker learns of the event afterwards. -/
def indirect : LearningScenario Ev := ⟨.described, .learnIndirect⟩

/-- In direct witness the speaker perceives the event as it happens, in the same place. -/
def direct : LearningScenario Ev := ⟨.described, .learnDirect⟩

/-- With smoke from the chimney, (25b), the speaker perceives the evidence at the same time
from elsewhere. -/
def smoke : LearningScenario Ev := ⟨.described, .learnSmoke⟩

/-- The two events of the smoke scenario are distinct and simultaneous. -/
example : smoke.described ≠ smoke.learning ∧ τ smoke.described = τ smoke.learning :=
  ⟨by decide, rfl⟩

/-- The location of every event is `here` except the seeing of the smoke. -/
def loc : Ev → Place
  | .learnSmoke => .there
  | _ => .here

theorem felicity :
    spatiotemporallyDistant loc indirect.described indirect.learning ∧
      spatiotemporallyDistant loc smoke.described smoke.learning ∧
      ¬ spatiotemporallyDistant loc direct.described direct.learning := by
  decide

/-- Direct witness fails both disjuncts of Definition 24. -/
theorem direct_not_distant (loc : Ev → L) (h : loc direct.described = loc direct.learning) :
    ¬ spatiotemporallyDistant loc direct.described direct.learning := by
  rintro (hd | hl)
  · exact hd (by decide)
  · exact hl h

/-- The two constraints of (74b) are independent, as the indirect and smoke scenarios show. -/
theorem smoke_no_tense_ordering :
    (τ indirect.described).Precedes (τ indirect.learning) ∧
      ¬ (τ smoke.described).Precedes (τ smoke.learning) ∧
      temporallyDisjoint indirect.described indirect.learning ∧
      ¬ temporallyDisjoint smoke.described smoke.learning := by
  decide

end Koev2017
