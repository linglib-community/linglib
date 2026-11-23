/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.PFun
public import Mathlib.Logic.Function.Basic
public import Linglib.Semantics.ArgumentStructure.MapArgs

/-!
# Control and raising

On the analysis of Montague, Bach, Dowty and Chierchia the complement of *try*, *persuade* or
*seem* denotes a property, and the predicate denotes a relation `R : (E → Φ) → X → Ψ` between a
property and its other arguments `X`, with `Φ` the propositions. What is called control and
raising are then two answers to how much of the property the relation reads. A *role* is a
partial function `θ : X →. E` from the arguments to the individual among them that bears it, an
argument position being the case of a total function. The relation is *controlled* at `θ`,
`IsControlledAt R θ`, when it reads the property only at the bearer of the role, and *raising* at
a position `c`, `IsRaisingAt R c`, when it reads only the proposition `P (c x)`.

A raising relation is controlled, a relation controlled at a position is exactly a relation to a
proposition and the arguments (`isControlledAt_coe_iff`), and a raising relation is exactly a
property of propositions (`isRaisingAt_iff`), which entails nothing of `c x` that it does not
entail of everything (`IsRaisingAt.le_of_le`): the argument is not a semantic argument of the
relation, as no participant of a raising verb fills the slot it raises into
(`Diathesis.IsRaising`). A controlled relation stays controlled when its arguments are
substituted (`IsControlledAt.comapArgs`) and when arguments are closed existentially along a map
through which the role factors (`IsControlledAt.mapArgs`).

A relation to a proposition `S : Φ → X → Ψ` gives the relation to a property `atRole θ S`, which
is `S (P e) x` where `e` bears the role among the arguments `x` and `⊥` where nothing does. It is
controlled at `θ` (`isControlledAt_atRole`), raising at a position when `S` does not depend on
the arguments (`isRaisingAt_atRole`), and `⊥` when nothing bears the role
(`atRole_eq_bot_of_dom_eq_empty`).

## Implementation notes

* `IsRaisingAt` and `IsControlledAt` are predicates on the bare relation, as `Monotone` is on a
  function, and a relation that reads the whole property satisfies neither. Equality in `Φ` is
  logical equivalence when propositions are sets of worlds.
* A role is partial so that a relation may have arguments among which nothing bears it, as the
  passive of a verb whose subject controls has; a relation controlled at a role does not read its
  property there at all. Chierchia's thematic role is such a function, a thematic relation of
  `ArgumentStructure/ThematicRole.lean` that is functional, and the participant in a slot is the
  case of a projection.
* `atRole θ S` is the join of `S (P e) x` over the bearers `e` of the role, of which there is at
  most one. The meet over them is `⊤` where nothing bears the role, the reading on which a schema
  of control says nothing of arguments without a controller.

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

/-- A relation to a property is raising at `c` when it depends only on the proposition the
property forms with `c x`: two properties forming one proposition with two arguments are related
alike. -/
def IsRaisingAt (R : (E → Φ) → X → Ψ) (c : X → E) : Prop :=
  ∀ ⦃P Q : E → Φ⦄ ⦃x y : X⦄, P (c x) = Q (c y) → R P x = R Q y

/-- A relation to a property is controlled at the role `θ` when it depends on the property only
through the proposition it forms with the bearer of the role. -/
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

/-- A relation is controlled at the position `c` exactly when it is a relation to a proposition,
taken at the proposition the property forms with `c x`. -/
theorem isControlledAt_coe_iff :
    IsControlledAt R (c : X →. E) ↔ ∃ R' : Φ → X → Ψ, ∀ P x, R P x = R' (P (c x)) x :=
  isControlledAt_coe.trans ⟨fun h ↦ ⟨fun φ x ↦ R (fun _ ↦ φ) x, fun _ _ ↦ h rfl⟩,
    fun ⟨R', h⟩ P Q x hPQ ↦ by rw [h, h, hPQ]⟩

open Classical in
/-- A relation is raising at `c` exactly when it is a property of propositions, taken at the
proposition the property forms with `c x`. -/
theorem isRaisingAt_iff [Nonempty Ψ] :
    IsRaisingAt R c ↔ ∃ S : Φ → Ψ, ∀ P x, R P x = S (P (c x)) :=
  ⟨fun h ↦ ⟨fun φ ↦ if hX : Nonempty X then R (fun _ ↦ φ) hX.some else Classical.arbitrary Ψ,
      fun P x ↦ by simp only [(⟨x⟩ : Nonempty X), ↓reduceDIte]; exact h rfl⟩,
    fun ⟨S, h⟩ P Q x y hPQ ↦ by rw [h, h, hPQ]⟩

/-- What a raising relation entails of the argument it is raising at, it entails of every entity
some argument takes there: its meaning does not depend on that argument as such. -/
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

/-- The relation to a property that the relation to a proposition `S` gives at the role `θ`: `S`
of the proposition that the bearer of the role has the property, and `⊥` where nothing bears
it. -/
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

/-- The relation of a position is raising there when the relation to a proposition does not
depend on the arguments. -/
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
