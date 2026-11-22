module

public import Linglib.Core.GameTheory.Equilibrium
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

The communicator and the members of the audience choose their contingency plans in a coordination
problem whose shared payoff is the probability that every member makes the preferred response.
Every signaling system is a coordination equilibrium of it
(`isCoordinationEquilibrium_plans`), and a proper one when each state can occur: each agent does
worse by any other plan (`isStrictEquilibrium_plans`).

The sexton of the Old North Church and Paul Revere have three plans each, among six signaling
systems on three states and three signals. The combinations that ensure the right warning are
`⟨R1, C1⟩`, `⟨R2, C2⟩` and `⟨R3, C3⟩` (`success_sexton_revere_eq_one_iff`), and the combinations
that ensure a wrong one are `⟨R1, C2⟩` and `⟨R2, C1⟩` (`success_sexton_revere_eq_zero_iff`).

## Implementation notes

* A proper equilibrium is `IsStrictEquilibrium`. The agents are indexed by `Option J`, with `none`
  the communicator and `J` the audience, which must have a member for the equilibrium to be
  proper.
* A member of the audience whose plan is not defined at the signal given does not make the
  preferred response. A plan that agrees with the signaling system's on the signals in use is
  that plan, since both are one-to-one onto the responses.
* The plans are indexed by `Fin 3`, the sexton's `Ri` and Paul Revere's `Ci` sharing the index
  `i - 1`, so that the diagonal of the figure is `i = j`.
* The payoffs of the coordination problem between the sexton and Paul Revere are formalized as
  expected success at a prior under which each state can occur: success is one, zero, or strictly
  between where the figure prints `1`, `0` or `.5`.

## TODO

* One-sided signaling, signaling conventions as regularities in a population, and the meanings of
  signals.

## References

* [lewis-1969]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Lewis1969

/-! ### The coordination problem of choosing contingency plans -/

section Coordination

universe u

variable {S R M : Type u} {J : Type*} {F : S ≃ R}

/-- The contingency plans open to the communicator, `none`, and to each member `some j` of the
audience. -/
abbrev Plans (S R M : Type u) (J : Type*) : Option J → Type u
  | none => S → M
  | some _ => M ≃. R

variable [MeasurableSpace S]

/-- The payoff of a combination of contingency plans, shared by all: the probability that every
member of the audience makes the preferred response. -/
noncomputable def payoff (pr : Measure S) (F : S ≃ R) (a : ∀ o, Plans S R M J o) : ℝ :=
  pr.real {s | ∀ j, (a (some j) : M ≃. R) ((a none : S → M) s) = some (F s)}

/-- The combination of contingency plans in which the communicator and every member of the
audience follow a signaling system. -/
def plans (A : SignalingSystem F M) (J : Type*) : ∀ o, Plans S R M J o
  | none => A.communicator
  | some _ => A.audience

variable (pr : Measure S) [IsProbabilityMeasure pr]

private theorem measureReal_lt_one [MeasurableSingletonClass S] {T : Set S} {s : S} (hs : s ∉ T) (hpr : pr {s} ≠ 0) :
    pr.real T < 1 := by
  have h : pr.real T + pr.real {s} ≤ 1 := by
    rw [← measureReal_union (Set.disjoint_singleton_right.2 hs) (.singleton s)]
    exact measureReal_le_one
  have : 0 < pr.real {s} := ENNReal.toReal_pos hpr (measure_ne_top _ _)
  linarith

theorem payoff_plans (A : SignalingSystem F M) :
    payoff pr F (plans A J) = 1 := by
  rw [payoff, show {s | ∀ j : J, (plans A J (some j) : M ≃. R) ((plans A J none : S → M) s) =
    some (F s)} = Set.univ from Set.eq_univ_of_forall fun s _ ↦ A.audience_communicator s]
  exact probReal_univ

/-- Every signaling system is a coordination equilibrium of the choice of contingency plans. -/
theorem isCoordinationEquilibrium_plans [DecidableEq J] (A : SignalingSystem F M) :
    IsCoordinationEquilibrium (fun _ : Option J ↦ payoff pr F) (plans A J) :=
  isCoordinationEquilibrium_const_of_forall_le fun _ ↦ by
    rw [payoff_plans]
    exact measureReal_le_one

/-- When each state can occur, every signaling system is a proper equilibrium of the choice of
contingency plans: the communicator and each member of the audience do worse by any other plan. -/
theorem isStrictEquilibrium_plans [MeasurableSingletonClass S] [DecidableEq J] [Nonempty J]
    (hpr : ∀ s, pr {s} ≠ 0) (A : SignalingSystem F M) :
    IsStrictEquilibrium (fun _ : Option J ↦ payoff pr F) (plans A J) := by
  rintro (_ | j) x hx <;> change payoff pr F _ < payoff pr F (plans A J) <;>
    rw [payoff_plans]
  · obtain ⟨s, hs⟩ : ∃ s, (x : S → M) s ≠ A.communicator s := by
      by_contra h
      exact hx (funext fun s ↦ not_not.1 (not_exists.1 h s))
    obtain ⟨j⟩ := ‹Nonempty J›
    refine measureReal_lt_one pr (s := s) (fun h ↦ hs ?_) (hpr s)
    have := h j
    rw [Function.update_self, Function.update_of_ne (by simp)] at this
    exact ((A.audience_eq_some_iff).1 this).symm.trans (by rw [F.symm_apply_apply])
  · obtain ⟨s, hs⟩ : ∃ s, (x : M ≃. R) (A.communicator s) ≠ some (F s) := by
      by_contra h
      exact hx (congrArg SignalingSystem.audience
        (SignalingSystem.ext (A := ⟨A.communicator, x, fun s ↦ not_not.1 (not_exists.1 h s)⟩)
          (B := A) rfl))
    refine measureReal_lt_one pr (s := s) (fun h ↦ hs ?_) (hpr s)
    have := h j
    rwa [Function.update_self, Function.update_of_ne (by simp)] at this

end Coordination


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
