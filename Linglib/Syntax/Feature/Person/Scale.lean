/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Feature.Person.Decomposition

/-!
# The binary person scale

The *binary person scale* ranks the first and second persons, the participants in the speech
act, above the third. It is Haspelmath's person scale, locuphoric above aliophoric, and the cut
that Bonet's strong person-case constraint draws. A more prominent person is never lower on the
scale, and a scenario is downstream on it exactly when its higher-ranked argument alone is a
participant.

## Main definitions

* `Scale`: locuphoric or aliophoric, the locuphoric higher.
* `Scale.ofParticipants s`: the place of the participant set `s`, locuphoric when it includes a
  role.
* `Person.toScale p`: the place of the person `p`.

## Main results

* `Person.toScale_mono`: a more prominent person is never lower on the scale.
* `kind_map_toScale_eq_downstream_iff`: a scenario is downstream on the scale exactly when its
  higher-ranked argument alone is a participant.

## References

* [haspelmath-2021]
* [bonet-1991]
-/

@[expose] public section

namespace Person

-- [haspelmath-2021] (8a).
/-- The binary person scale ranks the first and second persons, the locuphoric ones, above the
third, the aliophoric. -/
inductive Scale where
  /-- The third person. -/
  | aliophoric
  /-- The first and second persons. -/
  | locuphoric
  deriving DecidableEq, Repr, Fintype

namespace Scale

/-- The scale orders `aliophoric < locuphoric`. -/
instance : LinearOrder Scale := LinearOrder.lift' (·.ctorIdx) (by decide)

/-- The scale is bounded, `⊥ = aliophoric` and `⊤ = locuphoric`. -/
instance : BoundedOrder Scale where
  top := .locuphoric
  le_top := by decide
  bot := .aliophoric
  bot_le := by decide

instance : IsSimpleOrder Scale where
  exists_pair_ne := ⟨.aliophoric, .locuphoric, by decide⟩
  eq_bot_or_eq_top := by decide

end Scale

/-- The binary person scale as a person system: both roles have the top value, so a participant
set is `locuphoric` exactly when it includes a speech-act participant. -/
def Scale.ofParticipants : SupBotHom (Finset SpeechAct.Role) Scale := Finset.supBotLift fun _ ↦ ⊤

theorem Scale.ofParticipants_eq_top_iff {s : Finset SpeechAct.Role} :
    Scale.ofParticipants s = ⊤ ↔ Bears s .participant := by
  revert s; decide

/-- The place of a person on the scale: locuphoric for the first and the second. -/
def toScale (p : Person) : Scale := if p ≠ .third then .locuphoric else .aliophoric

/-- The place of a participant set's person on the scale is the scale's value at the set. -/
theorem toScale_ofParticipants (s : Finset SpeechAct.Role) :
    (ofParticipants s).toScale = Scale.ofParticipants s := by
  revert s; decide

@[simp] theorem toScale_eq_locuphoric_iff {p : Person} :
    p.toScale = .locuphoric ↔ p ≠ .third := by
  revert p; decide

@[simp] theorem toScale_eq_aliophoric_iff {p : Person} :
    p.toScale = .aliophoric ↔ p = .third := by
  revert p; decide

/-- A more prominent person is never lower on the scale. -/
theorem toScale_mono {p q : Person} (h : p.prominence ≤ q.prominence) :
    p.toScale ≤ q.toScale := by
  revert h; cases p <;> cases q <;> decide

/-- A scenario is downstream on the binary person scale exactly when its higher-ranked argument
alone is a speech-act participant. -/
theorem kind_map_toScale_eq_downstream_iff {s : Clause.Scenario Person} :
    (s.map toScale).kind = .downstream ↔ s.high ≠ .third ∧ s.low = .third := by
  rw [Clause.Scenario.kind_eq_downstream_iff_eq_top, Clause.Scenario.ext_iff]
  exact and_congr toScale_eq_locuphoric_iff toScale_eq_aliophoric_iff

end Person
