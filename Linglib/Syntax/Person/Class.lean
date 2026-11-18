module

public import Mathlib.Order.Atoms
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Person.Features

/-!
# The binary person scale

The binary person scale puts the speech-act participants, first and second person, above the rest:
Haspelmath's person scale, locuphoric above aliophoric in his terms, and the cut that Bonet's
strong person-case constraint draws. It is [a person system](##Person.Class.ofParticipants) in
which both roles have the top value, [the coarsening of `Person.prominence` at the participant
level](##Person.toClass_mono), and
[a scenario is downstream on it](##Person.kind_map_toClass_eq_downstream_iff) exactly when its
higher-ranked argument alone is a speech-act participant.

## References

* [haspelmath-2021]
* [bonet-1991]
-/

@[expose] public section

namespace Person

-- [haspelmath-2021] (8a).
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

/-- The binary person scale as a person system: both roles have the top value, so a participant
set is `participant` exactly when it includes a speech-act participant. -/
def Class.ofParticipants : SupBotHom (Finset SpeechAct.Role) Class := Finset.supBotLift fun _ ↦ ⊤

theorem Class.ofParticipants_eq_top_iff {s : Finset SpeechAct.Role} :
    Class.ofParticipants s = ⊤ ↔ Bears s .participant := by
  revert s; decide

/-- The class of a person is `participant` exactly when it is a speech-act participant. -/
def toClass (p : Person) : Class := if p.IsSAP then .participant else .nonParticipant

/-- The class of a participant set's person is its value on the binary person scale. -/
theorem toClass_ofParticipants (s : Finset SpeechAct.Role) :
    (ofParticipants s).toClass = Class.ofParticipants s := by
  revert s; decide

@[simp] theorem toClass_eq_participant_iff {p : Person} : p.toClass = .participant ↔ p.IsSAP := by
  revert p; decide

@[simp] theorem toClass_eq_nonParticipant_iff {p : Person} :
    p.toClass = .nonParticipant ↔ ¬ p.IsSAP := by
  revert p; decide

/-- The class is the coarsening of prominence at the participant level. -/
theorem toClass_mono {p q : Person} (h : p.prominence ≤ q.prominence) :
    p.toClass ≤ q.toClass := by
  revert h; cases p <;> cases q <;> decide

/-- A scenario is downstream on the binary person scale exactly when its higher-ranked argument
alone is a speech-act participant. -/
theorem kind_map_toClass_eq_downstream_iff {s : Clause.Scenario Person} :
    (s.map toClass).kind = .downstream ↔ s.high.IsSAP ∧ ¬ s.low.IsSAP := by
  rw [Clause.Scenario.kind_eq_downstream_iff_eq_top, Clause.Scenario.ext_iff]
  exact and_congr toClass_eq_participant_iff toClass_eq_nonParticipant_iff

end Person
