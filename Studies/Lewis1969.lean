module

public import Linglib.Pragmatics.SignalingGame.Basic
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Lewis (1969): Convention

In a two-sided signaling problem exactly one of several states holds, and the communicator, who
can tell which, gives one of several signals to an audience that then makes a response. A
one-to-one function `F` from the states onto the responses gives the response everyone prefers at
each state. A communicator's contingency plan is a function from states to signals, and an
audience's contingency plan is a one-to-one function from some of the signals to responses. The two
form a signaling system, `Lewis1969.SignalingSystem`, when the audience's response to the
communicator's signal is `F s` at every state `s`.

The audience's plan of a signaling system is defined on exactly the signals its communicator uses
(`SignalingSystem.isSome_audience_iff`) and is determined by the communicator's plan
(`SignalingSystem.ext`). A communicator's plan belongs to a signaling system exactly when it is
one-to-one, and an audience's plan exactly when every response answers some signal. Signaling
systems therefore correspond to the injections of the states into the signals
(`SignalingSystem.equivEmbedding`), and with $m$ states and $n$ signals there are $n!/(n-m)!$ of
them (`SignalingSystem.card_eq`).

A permutation of the signals acts on a signaling system by relabelling the communicator's signals
and undoing the relabelling before the audience responds. With finitely many states any two
signaling systems differ by such a relabelling, and with a state and two signals none is fixed by
all of them
(`SignalingSystem.exists_smul_ne`). A signaling system has `SignalingGame.success` one at every
prior (`SignalingSystem.success_eq_one`), whereas a strategy that every relabelling leaves
unchanged succeeds no more often than the likeliest state occurs
(`SignalingGame.success_le_of_forall_map_eq`).

The sexton of the Old North Church and Paul Revere have three plans each. The combinations that
ensure the right warning are `⟨R1, C1⟩`, `⟨R2, C2⟩` and `⟨R3, C3⟩`
(`success_sexton_revere_eq_one_iff`).

## Implementation notes

* The audience's plan is a partial equivalence `M ≃. R`, a one-to-one function from part of the
  signals into the responses together with its inverse.
* The count is of pairs of plans, stated as `(Nat.card M).descFactorial (Nat.card S)`, which is
  $n!/(n-m)!$ when $m \le n$ (`Nat.descFactorial_eq_div`) and zero otherwise.
* The relabellings are permutations of all the signals. With finitely many states every one-to-one
  function from the signals a plan uses into the signals extends to one.
* Success is stated for a response at every signal that agrees with the audience's plan where the
  plan is defined, and identifies each response with the state it is preferred in.
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

open Function MeasureTheory ProbabilityTheory

namespace Lewis1969

variable {S R M : Type*} {F : S ≃ R}

/-- A signaling system for the preferred dependence `F` of responses on states: a communicator's
contingency plan from states to signals and an audience's contingency plan, a one-to-one function
from some of the signals to responses, whose composite is `F`. -/
structure SignalingSystem (F : S ≃ R) (M : Type*) where
  /-- The communicator's contingency plan. -/
  communicator : S → M
  /-- The audience's contingency plan. -/
  audience : M ≃. R
  audience_communicator (s : S) : audience (communicator s) = some (F s)

namespace SignalingSystem

attribute [simp] audience_communicator

@[simp]
theorem symm_audience (A : SignalingSystem F M) (s : S) :
    A.audience.symm (F s) = some (A.communicator s) :=
  A.audience.eq_some_iff.2 (A.audience_communicator s)

theorem communicator_injective (A : SignalingSystem F M) : Injective A.communicator :=
  fun s t h ↦ F.injective <| Option.some_injective _ <| by
    rw [← A.audience_communicator, h, A.audience_communicator]

theorem audience_eq_some_iff (A : SignalingSystem F M) {m : M} {r : R} :
    A.audience m = some r ↔ A.communicator (F.symm r) = m := by
  have h := A.symm_audience (F.symm r)
  rw [F.apply_symm_apply] at h
  rw [← A.audience.eq_some_iff, h, Option.some_inj]

theorem isSome_audience_iff (A : SignalingSystem F M) {m : M} :
    (A.audience m).isSome ↔ m ∈ Set.range A.communicator := by
  simp only [Option.isSome_iff_exists, audience_eq_some_iff, Set.mem_range]
  exact ⟨fun ⟨r, h⟩ ↦ ⟨_, h⟩, fun ⟨s, h⟩ ↦ ⟨F s, by rwa [F.symm_apply_apply]⟩⟩

@[ext]
theorem ext {A B : SignalingSystem F M} (h : A.communicator = B.communicator) : A = B := by
  have h' : A.audience = B.audience := PEquiv.ext fun m ↦ Option.ext fun r ↦ by
    rw [A.audience_eq_some_iff, B.audience_eq_some_iff, h]
  obtain ⟨c, a, ha⟩ := A
  obtain ⟨c', a', ha'⟩ := B
  dsimp only at h h'
  subst h h'
  rfl

/-- The signaling system of a one-to-one communicator's plan `f`, whose audience answers the
signal `f s` with the response `F s`. -/
noncomputable def ofEmbedding (F : S ≃ R) (f : S ↪ M) : SignalingSystem F M where
  communicator := f
  audience :=
    { toFun := fun m ↦ (partialInv f m).map F
      invFun := fun r ↦ some (f (F.symm r))
      inv := fun m r ↦ by
        rw [Option.some_inj, Option.map_eq_some_iff]
        constructor
        · rintro rfl
          exact ⟨F.symm r, partialInv_left f.injective _, F.apply_symm_apply r⟩
        · rintro ⟨s, hs, rfl⟩
          rw [F.symm_apply_apply]
          exact (f.injective.isPartialInv s m).1 hs }
  audience_communicator s := congrArg (Option.map F) (partialInv_left f.injective s)

/-- Signaling systems correspond to the one-to-one communicator's plans. -/
noncomputable def equivEmbedding : SignalingSystem F M ≃ (S ↪ M) where
  toFun A := ⟨A.communicator, A.communicator_injective⟩
  invFun := ofEmbedding F
  left_inv _ := ext rfl
  right_inv _ := rfl

@[simp]
theorem coe_equivEmbedding (A : SignalingSystem F M) : ⇑(equivEmbedding A) = A.communicator :=
  rfl

/-- A communicator's plan belongs to a signaling system exactly when it is one-to-one. -/
theorem exists_communicator_eq_iff {f : S → M} :
    (∃ A : SignalingSystem F M, A.communicator = f) ↔ Injective f :=
  ⟨by rintro ⟨A, rfl⟩; exact A.communicator_injective, fun h ↦ ⟨ofEmbedding F ⟨f, h⟩, rfl⟩⟩

theorem exists_audience_eq_iff {g : M ≃. R} :
    (∃ A : SignalingSystem F M, A.audience = g) ↔ ∀ r, (g.symm r).isSome := by
  refine ⟨?_, fun h ↦ ⟨⟨fun s ↦ (g.symm (F s)).get (h _), g, fun s ↦ ?_⟩, rfl⟩⟩
  · rintro ⟨A, rfl⟩ r
    have h := A.symm_audience (F.symm r)
    rw [F.apply_symm_apply] at h
    rw [h, Option.isSome_some]
  · exact g.eq_some_iff.1 (Option.some_get _).symm

/-- With `m` states and `n` signals there are `n! / (n - m)!` signaling systems. -/
theorem card_eq [Finite S] [Finite M] :
    Nat.card (SignalingSystem F M) = (Nat.card M).descFactorial (Nat.card S) := by
  classical
  have := Fintype.ofFinite S
  have := Fintype.ofFinite M
  rw [Nat.card_congr equivEmbedding, Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-! ### Relabelling the signals -/

/-- A permutation of the signals acts on a signaling system: the communicator sends the relabelled
signal and the audience undoes the relabelling before responding. -/
instance : MulAction (Equiv.Perm M) (SignalingSystem F M) where
  smul π A :=
    { communicator := π ∘ A.communicator
      audience := π.symm.toPEquiv.trans A.audience
      audience_communicator := fun s ↦ (PEquiv.trans_eq_some ..).2
        ⟨A.communicator s, by simp, A.audience_communicator s⟩ }
  one_smul _ := ext rfl
  mul_smul _ _ _ := ext rfl

@[simp]
theorem smul_communicator (π : Equiv.Perm M) (A : SignalingSystem F M) :
    (π • A).communicator = π ∘ A.communicator :=
  rfl

@[simp]
theorem smul_audience (π : Equiv.Perm M) (A : SignalingSystem F M) :
    (π • A).audience = π.symm.toPEquiv.trans A.audience :=
  rfl

theorem equivEmbedding_smul (π : Equiv.Perm M) (A : SignalingSystem F M) :
    equivEmbedding (π • A) = π • equivEmbedding A :=
  rfl

/-- Any two signaling systems differ by a relabelling of the signals. -/
instance [Finite S] : MulAction.IsPretransitive (Equiv.Perm M) (SignalingSystem F M) where
  exists_smul_eq A B := by
    obtain ⟨π, h⟩ := Equiv.Perm.exists_smul_eq_embedding (equivEmbedding A) (equivEmbedding B)
    exact ⟨π, equivEmbedding.injective (by rw [equivEmbedding_smul, h])⟩

/-- No signaling system is fixed by every relabelling of the signals: each has an alternative. -/
theorem exists_smul_ne [Nonempty S] [Nontrivial M] (A : SignalingSystem F M) :
    ∃ π : Equiv.Perm M, π • A ≠ A := by
  classical
  obtain ⟨s⟩ := ‹Nonempty S›
  obtain ⟨m, hm⟩ := exists_ne (A.communicator s)
  refine ⟨Equiv.swap (A.communicator s) m, fun h ↦ hm ?_⟩
  simpa using congrFun (congrArg communicator h) s

/-! ### Success -/

section success

variable [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S] [MeasurableSpace M]
  [Countable M] [MeasurableSingletonClass M] (pr : Measure S) [IsProbabilityMeasure pr]

/-- In a signaling system the audience's response is the preferred one at every state, whatever
the audience does at signals outside its plan. -/
theorem success_eq_one (A : SignalingSystem F M) {g : M → R}
    (hg : ∀ m r, A.audience m = some r → g m = r) :
    SignalingGame.success pr (.deterministic A.communicator .of_discrete)
      (.deterministic (F.symm ∘ g) .of_discrete) = 1 := by
  rw [SignalingGame.success_deterministic_eq_one_iff]
  exact .of_forall fun s ↦ by simp [hg _ _ (A.audience_communicator s)]

end success

end SignalingSystem

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
