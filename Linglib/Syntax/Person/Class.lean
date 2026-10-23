module

public import Mathlib.Order.Atoms
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Person.Features

/-!
# The binary person scale

The load-bearing cut of person prominence puts the speech-act participants, first and second
person, above the rest. It is Haspelmath's person scale (8a), locuphoric above aliophoric in
his terms, the cut that Bonet's strong person-case constraint draws, and the coarsening of
`Person.prominence` at the participant level.

## Main declarations

* `Person.Class`: `nonParticipant < participant`, a two-element bounded linear order.
* `Person.toClass`: the class of a person, `participant` exactly when it `IsSAP`, and
  `toClass_mono` for its agreement with `prominence`.
* `Person.kind_map_toClass_eq_downstream_iff`: a scenario is downstream on the binary scale
  exactly when its higher-ranked argument alone is a speech-act participant.

## References

* [haspelmath-2021]
* [bonet-1991]
-/

@[expose] public section

namespace Person

/-- The binary person scale ranks speech-act participants above non-participants. -/
inductive Class where
  | nonParticipant
  | participant
  deriving DecidableEq, Repr, Fintype

namespace Class

/-- The scale orders `nonParticipant < participant`. -/
instance : LinearOrder Class := LinearOrder.lift' (·.ctorIdx) (by decide)

/-- The scale is bounded, `⊥ = nonParticipant` and `⊤ = participant`. -/
instance : BoundedOrder Class where
  top := .participant
  le_top := by decide
  bot := .nonParticipant
  bot_le := by decide

instance : IsSimpleOrder Class where
  exists_pair_ne := ⟨.nonParticipant, .participant, by decide⟩
  eq_bot_or_eq_top := by decide

end Class

/-- The class of a person is `participant` exactly when it is a speech-act participant. -/
def toClass (p : Person) : Class := if p.IsSAP then .participant else .nonParticipant

@[simp] theorem toClass_eq_participant_iff {p : Person} : p.toClass = .participant ↔ p.IsSAP := by
  revert p; decide

@[simp] theorem toClass_eq_nonParticipant_iff {p : Person} :
    p.toClass = .nonParticipant ↔ ¬ p.IsSAP := by
  revert p; decide

theorem toClass_mono {p q : Person} (h : p.prominence ≤ q.prominence) :
    p.toClass ≤ q.toClass := by
  revert h; cases p <;> cases q <;> decide

theorem kind_map_toClass_eq_downstream_iff {s : Clause.Scenario Person} :
    (s.map toClass).kind = .downstream ↔ s.high.IsSAP ∧ ¬ s.low.IsSAP := by
  rw [Clause.Scenario.kind_eq_downstream_iff_eq_top, Clause.Scenario.ext_iff]
  exact and_congr toClass_eq_participant_iff toClass_eq_nonParticipant_iff

end Person
