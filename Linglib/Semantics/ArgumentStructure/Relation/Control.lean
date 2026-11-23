/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.PFun
public import Mathlib.Logic.Function.Basic
public import Linglib.Semantics.ArgumentStructure.Relation.MapArgs

/-!
# Control and raising

The complement of *try*, *persuade* or *seem* can be analyzed as denoting a property. The verb
then denotes a relation `R : (E → Φ) → X → Ψ` between a property and the verb's other arguments.
Here `E` is the type of entities, `Φ` and `Ψ` are types of propositions, and `X` is the type of
the other arguments. This file defines what it means for such a relation to be controlled or
raising.

A *role* is a partial function `θ : X →. E`. It picks out one entity among the arguments, when
there is one. An argument position is a total function `c : X → E`, which we coerce to a role.

* `IsControlledAt R θ` says that `R P x` depends on the property `P` only through its value at
  the entity `θ x`. If `θ x` is undefined, `R P x` does not depend on `P` at all.
* `IsRaisingAt R c` says that `R P x` depends on `P` and `x` only through the proposition
  `P (c x)`.

We show that a raising relation is controlled (`IsRaisingAt.isControlledAt`). A relation is
controlled at a position `c` exactly when `R P x = R' (P (c x)) x` for some `R'`
(`isControlledAt_coe_iff`). It is raising at `c` exactly when `R P x = S (P (c x))` for some `S`
(`isRaisingAt_iff`). A raising relation entails nothing about `c x` that it does not entail about
every entity (`IsRaisingAt.le_of_le`).

Given a role `θ` and a relation to a proposition `S : Φ → X → Ψ`, we define `atRole θ S`. When
`e` is the value of `θ x`, we have `atRole θ S P x = S (P e) x`. When `θ x` is undefined, we have
`atRole θ S P x = ⊥`. We show that `atRole θ S` is controlled at `θ` (`isControlledAt_atRole`),
and that it is `⊥` when `θ` is nowhere defined (`atRole_eq_bot_of_dom_eq_empty`).

A controlled relation stays controlled under `comapArgs` (`IsControlledAt.comapArgs`), and under
`mapArgs` along a map that the role factors through (`IsControlledAt.mapArgs`).

## Implementation notes

* `IsControlledAt` and `IsRaisingAt` are predicates on a bare function, like `Monotone`. A
  relation that reads the whole property satisfies neither.
* A role is partial because some relations have arguments among which no entity bears the role.
  The passive of a verb whose subject controls is an example.
* Equality in `Φ` is logical equivalence when propositions are sets of worlds.

## References

* [dowty-1985]
* [bach-1979]
* [chierchia-1984]
* [chierchia-1989]
* [stiebels-2007]
-/

@[expose] public section

open Function

namespace ArgumentStructure

variable {E Φ Ψ W X Y : Type*} {R : (E → Φ) → X → Ψ} {θ : X →. E} {c : X → E} {x : X}

/-! ### Control and raising -/

/-- A relation is raising at the position `c` when `R P x` depends on `P` and `x` only through
the proposition `P (c x)`. -/
def IsRaisingAt (R : (E → Φ) → X → Ψ) (c : X → E) : Prop :=
  ∀ ⦃P Q : E → Φ⦄ ⦃x y : X⦄, P (c x) = Q (c y) → R P x = R Q y

/-- A relation is controlled at the role `θ` when `R P x` depends on `P` only through its value
at the entity `θ x`. -/
def IsControlledAt (R : (E → Φ) → X → Ψ) (θ : X →. E) : Prop :=
  ∀ ⦃P Q : E → Φ⦄ ⦃x : X⦄, (∀ e ∈ θ x, P e = Q e) → R P x = R Q x

theorem isControlledAt_coe : IsControlledAt R (c : X →. E) ↔
    ∀ ⦃P Q : E → Φ⦄ ⦃x : X⦄, P (c x) = Q (c x) → R P x = R Q x :=
  ⟨fun h _ _ _ hPQ ↦ h fun _ he ↦ Part.mem_some_iff.1 he ▸ hPQ,
    fun h _ _ _ hPQ ↦ h (hPQ _ (Part.mem_some _))⟩

theorem IsRaisingAt.isControlledAt (h : IsRaisingAt R c) : IsControlledAt R c :=
  isControlledAt_coe.2 fun _ _ _ hPQ ↦ h hPQ

theorem isControlledAt_coe_iff_forall_factorsThrough :
    IsControlledAt R (c : X →. E) ↔ ∀ x, FactorsThrough (R · x) (eval (c x)) :=
  isControlledAt_coe.trans ⟨fun h _ _ _ hPQ ↦ h hPQ, fun h _ _ x hPQ ↦ h x hPQ⟩

/-- A relation is controlled at the position `c` exactly when `R P x = R' (P (c x)) x` for some
`R'`. -/
theorem isControlledAt_coe_iff :
    IsControlledAt R (c : X →. E) ↔ ∃ R' : Φ → X → Ψ, ∀ P x, R P x = R' (P (c x)) x :=
  isControlledAt_coe.trans ⟨fun h ↦ ⟨fun φ x ↦ R (fun _ ↦ φ) x, fun _ _ ↦ h rfl⟩,
    fun ⟨R', h⟩ P Q x hPQ ↦ by rw [h, h, hPQ]⟩

open Classical in
/-- A relation is raising at `c` exactly when `R P x = S (P (c x))` for some `S`. -/
theorem isRaisingAt_iff [Nonempty Ψ] :
    IsRaisingAt R c ↔ ∃ S : Φ → Ψ, ∀ P x, R P x = S (P (c x)) :=
  ⟨fun h ↦ ⟨fun φ ↦ if hX : Nonempty X then R (fun _ ↦ φ) hX.some else Classical.arbitrary Ψ,
      fun P x ↦ by simp only [(⟨x⟩ : Nonempty X), ↓reduceDIte]; exact h rfl⟩,
    fun ⟨S, h⟩ P Q x y hPQ ↦ by rw [h, h, hPQ]⟩

/-- If a raising relation entails `α (c x)` for its own arguments `x`, it entails `α (c y)` for
every `y`. -/
theorem IsRaisingAt.le_of_le [LE Ψ] (h : IsRaisingAt R c) {α : E → Ψ}
    (hα : ∀ P x, R P x ≤ α (c x)) (P : E → Φ) (x y : X) : R P x ≤ α (c y) :=
  h (Q := fun _ ↦ P (c x)) (y := y) rfl ▸ hα _ y

/-! ### Control along maps of the arguments -/

theorem IsControlledAt.comapArgs (h : IsControlledAt R θ) (σ : Y → X) :
    IsControlledAt (comapArgs σ R) fun y ↦ θ (σ y) :=
  fun _ _ _ hPQ ↦ h hPQ

theorem IsRaisingAt.comapArgs (h : IsRaisingAt R c) (σ : Y → X) :
    IsRaisingAt (comapArgs σ R) (c ∘ σ) :=
  fun _ _ _ _ hPQ ↦ h hPQ

variable [CompleteLattice Ψ]

theorem IsControlledAt.mapArgs {σ : X → Y} {θ' : Y →. E}
    (h : IsControlledAt R fun x ↦ θ' (σ x)) : IsControlledAt (mapArgs σ R) θ' :=
  fun _ _ _ hPQ ↦ iSup_congr fun _ ↦ iSup_congr fun hx ↦ h fun e he ↦ hPQ e (hx ▸ he)

/-! ### The relation of a role -/

/-- The relation to a property given by `S` at the role `θ`: it is `S (P e) x` when `e` is the
value of `θ x`, and `⊥` when `θ x` is undefined. -/
def atRole (θ : X →. E) (S : Φ → X → Ψ) : (E → Φ) → X → Ψ :=
  fun P x ↦ ⨆ e ∈ θ x, S (P e) x

variable {S : Φ → X → Ψ} {P : E → Φ} {e : E}

theorem atRole_apply_of_mem (he : e ∈ θ x) (S : Φ → X → Ψ) (P : E → Φ) :
    atRole θ S P x = S (P e) x :=
  le_antisymm (iSup₂_le fun _ he' ↦ Part.mem_unique he' he ▸ le_rfl)
    (le_iSup₂ (f := fun e _ ↦ S (P e) x) e he)

theorem atRole_apply_of_notMem_dom (hx : x ∉ θ.Dom) (S : Φ → X → Ψ) (P : E → Φ) :
    atRole θ S P x = ⊥ :=
  iSup₂_eq_bot.2 fun e he ↦ (hx (Part.dom_iff_mem.2 ⟨e, he⟩)).elim

theorem atRole_eq_bot_of_dom_eq_empty (hθ : θ.Dom = ∅) (S : Φ → X → Ψ) : atRole θ S = ⊥ := by
  funext P x
  exact atRole_apply_of_notMem_dom (by simp [hθ]) S P

theorem isControlledAt_atRole (θ : X →. E) (S : Φ → X → Ψ) : IsControlledAt (atRole θ S) θ :=
  fun _ _ _ hPQ ↦ iSup_congr fun e ↦ iSup_congr fun he ↦ by rw [hPQ e he]

/-- If `S` does not depend on the arguments, `atRole c S` is raising at the position `c`. -/
theorem isRaisingAt_atRole (c : X → E) (S : Φ → Ψ) :
    IsRaisingAt (atRole (c : X →. E) fun φ _ ↦ S φ) c := fun P Q x y hPQ ↦ by
  rw [atRole_apply_of_mem (θ := (c : X →. E)) (Part.mem_some (c x)),
    atRole_apply_of_mem (θ := (c : X →. E)) (Part.mem_some (c y)), hPQ]

theorem comapArgs_atRole (σ : Y → X) (θ : X →. E) (S : Φ → X → Ψ) :
    comapArgs σ (atRole θ S) = atRole (fun y ↦ θ (σ y)) fun φ y ↦ S φ (σ y) :=
  rfl

@[simp] theorem mem_atRole {S : Φ → X → Set W} {w : W} :
    w ∈ atRole θ S P x ↔ ∃ e ∈ θ x, w ∈ S (P e) x := by
  simp [atRole]

end ArgumentStructure
