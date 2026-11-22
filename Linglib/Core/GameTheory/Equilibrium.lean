module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Filter.Extr

/-!
# Equilibria of games in strategic form

A game in strategic form has agents `i : ι`, each with a type `A i` of strategies, and a payoff
`u i : (∀ i, A i) → β` for each agent on the combinations of strategies. A combination `a` is an
equilibrium when no agent gains by changing her own strategy alone,
`u i (Function.update a i x) ≤ u i a`. It is a coordination equilibrium when no agent gains by any
one agent's changing hers, and a strict equilibrium when every agent loses by changing her own.

A strict equilibrium and a coordination equilibrium are equilibria. When the agents share one
payoff, the equilibria are the coordination equilibria
(`isCoordinationEquilibrium_const_iff`), and they include every combination at which the payoff is
greatest (`isCoordinationEquilibrium_const_of_forall_le`).

## Implementation notes

There is no structure for a game: the predicates take the family of payoffs. The strict equilibria
are the proper equilibria of [lewis-1969], who also introduces coordination equilibria.

## References

* [nash-1951]
* [lewis-1969]
-/

@[expose] public section

open Function

variable {ι β : Type*} [DecidableEq ι] {A : ι → Type*} {u : ι → (∀ i, A i) → β} {v : (∀ i, A i) → β}
  {a : ∀ i, A i}

section LE

variable [LE β]

/-- A combination of strategies is an equilibrium when no agent gains by changing her own strategy
alone. -/
def IsEquilibrium (u : ι → (∀ i, A i) → β) (a : ∀ i, A i) : Prop :=
  ∀ i (x : A i), u i (update a i x) ≤ u i a

/-- A combination of strategies is a coordination equilibrium when no agent gains by any one
agent's changing her strategy alone. -/
def IsCoordinationEquilibrium (u : ι → (∀ i, A i) → β) (a : ∀ i, A i) : Prop :=
  ∀ i j (x : A j), u i (update a j x) ≤ u i a

theorem IsCoordinationEquilibrium.isEquilibrium (h : IsCoordinationEquilibrium u a) :
    IsEquilibrium u a :=
  fun i ↦ h i i

/-- Under a shared payoff the coordination equilibria are the equilibria. -/
theorem isCoordinationEquilibrium_const_iff :
    IsCoordinationEquilibrium (fun _ : ι ↦ v) a ↔ IsEquilibrium (fun _ : ι ↦ v) a :=
  ⟨IsCoordinationEquilibrium.isEquilibrium, fun h _ j ↦ h j⟩

/-- A combination at which a shared payoff is greatest is a coordination equilibrium. -/
theorem isCoordinationEquilibrium_const_of_forall_le (h : ∀ b, v b ≤ v a) :
    IsCoordinationEquilibrium (fun _ : ι ↦ v) a :=
  fun _ _ _ ↦ h _

end LE

/-- A combination of strategies is a strict equilibrium when every agent loses by changing her own
strategy alone. -/
def IsStrictEquilibrium [LT β] (u : ι → (∀ i, A i) → β) (a : ∀ i, A i) : Prop :=
  ∀ i (x : A i), x ≠ a i → u i (update a i x) < u i a

variable [Preorder β]

theorem IsStrictEquilibrium.isEquilibrium (h : IsStrictEquilibrium u a) : IsEquilibrium u a :=
  fun i x ↦ by
    by_cases hx : x = a i
    · rw [hx, update_eq_self]
    · exact (h i x hx).le

theorem isEquilibrium_iff_isMaxOn :
    IsEquilibrium u a ↔ ∀ i, IsMaxOn (fun x ↦ u i (update a i x)) Set.univ (a i) := by
  simp only [IsEquilibrium, isMaxOn_iff, Set.mem_univ, true_imp_iff, update_eq_self]
