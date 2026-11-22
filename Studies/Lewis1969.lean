module

public import Linglib.Pragmatics.SignalingGame.SignalingSystem

/-!
# Lewis (1969): Convention

In a two-sided signaling problem exactly one of several states holds, and the communicator, who
can tell which, gives one of several signals to an audience that then makes a response. A
one-to-one function from the states onto the responses gives the response everyone prefers at each
state. A communicator's contingency plan and an audience's contingency plan form a signaling
system, `SignalingSystem`, when they combine to give the preferred response at every state. The
plans that belong to signaling systems are the admissible ones
(`SignalingSystem.exists_communicator_eq_iff`, `SignalingSystem.exists_audience_eq_iff`), and with
$m$ states and $n$ signals there are $n!/(n-m)!$ signaling systems (`SignalingSystem.card_eq`),
any two of which differ by a one-to-one relabelling of the signals.

The sexton of the Old North Church and Paul Revere have three plans each, among six signaling
systems on three states and three signals. The combinations that ensure the right warning are
`⟨R1, C1⟩`, `⟨R2, C2⟩` and `⟨R3, C3⟩` (`success_sexton_revere_eq_one_iff`), and the combinations
that ensure a wrong one are `⟨R1, C2⟩` and `⟨R2, C1⟩` (`success_sexton_revere_eq_zero_iff`).

## Implementation notes

* The plans are indexed by `Fin 3`, the sexton's `Ri` and Paul Revere's `Ci` sharing the index
  `i - 1`, so that the diagonal of the figure is `i = j`.
* The payoffs of the coordination problem between the sexton and Paul Revere are formalized as
  expected success at a prior under which each state can occur: success is one, zero, or strictly
  between where the figure prints `1`, `0` or `.5`.

## TODO

* Every signaling system is a proper coordination equilibrium of the choice of contingency plans.
* One-sided signaling, signaling conventions as regularities in a population, and the meanings of
  signals.

## References

* [lewis-1969]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Lewis1969

/-! ### The sexton and Paul Revere -/

/-- What the sexton observes the redcoats doing. -/
inductive Redcoats
  | home | land | sea
  deriving DecidableEq, Fintype

/-- The number of lanterns the sexton hangs in the belfry. -/
inductive Lanterns
  | zero | one | two
  deriving DecidableEq, Fintype

instance : MeasurableSpace Redcoats := ⊤
instance : MeasurableSpace Lanterns := ⊤
instance : DiscreteMeasurableSpace Redcoats := ⟨fun _ ↦ trivial⟩
instance : DiscreteMeasurableSpace Lanterns := ⟨fun _ ↦ trivial⟩

/-- The sexton's contingency plans `R1`, `R2` and `R3`. -/
def sexton : Fin 3 → Redcoats → Lanterns
  | 0, .home => .zero | 0, .land => .one | 0, .sea => .two
  | 1, .home => .one | 1, .land => .two | 1, .sea => .zero
  | 2, .home => .one | 2, .land => .zero | 2, .sea => .two

/-- Paul Revere's contingency plans `C1`, `C2` and `C3`, each response named by the state it is
preferred in: going home, or warning that the redcoats are coming by land or by sea. -/
def revere : Fin 3 → Lanterns → Redcoats
  | 0, .zero => .home | 0, .one => .land | 0, .two => .sea
  | 1, .zero => .sea | 1, .one => .home | 1, .two => .land
  | 2, .zero => .land | 2, .one => .home | 2, .two => .sea

example : Nat.card (SignalingSystem (Equiv.refl Redcoats) Lanterns) = 6 := by
  rw [SignalingSystem.card_eq, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rfl

section figure

variable (pr : Measure Redcoats) [IsProbabilityMeasure pr]

/-- Figure 38: when each state can occur, the sexton's plan `Ri` and Paul Revere's plan `Cj`
ensure the right warning exactly when `i = j`. -/
theorem success_sexton_revere_eq_one_iff (hpr : ∀ s, pr {s} ≠ 0) (i j : Fin 3) :
    SignalingGame.success pr (.deterministic (sexton i) .of_discrete)
      (.deterministic (revere j) .of_discrete) = 1 ↔ i = j := by
  have h : (∀ s, revere j (sexton i s) = s) ↔ i = j := by decide +revert
  rw [SignalingGame.success_deterministic_eq_one_iff, ae_iff_of_countable, ← h]
  exact ⟨fun h s ↦ h s (hpr s), fun h s _ ↦ h s⟩

-- Figure 38: the combinations that ensure a wrong warning are `⟨R1, C2⟩` and `⟨R2, C1⟩`.
theorem success_sexton_revere_eq_zero_iff (hpr : ∀ s, pr {s} ≠ 0) (i j : Fin 3) :
    SignalingGame.success pr (.deterministic (sexton i) .of_discrete)
      (.deterministic (revere j) .of_discrete) = 0 ↔ i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 := by
  have h : (∀ s, revere j (sexton i s) ≠ s) ↔ i = 0 ∧ j = 1 ∨ i = 1 ∧ j = 0 := by decide +revert
  rw [SignalingGame.success_deterministic, measureReal_eq_zero_iff,
    measure_null_iff_singleton (Set.to_countable _), ← h]
  exact ⟨fun h s hs ↦ hpr s (h s hs), fun h s hs ↦ absurd hs (h s)⟩

end figure

end Lewis1969
