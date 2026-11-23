/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Maps of a relation's arguments

A verb denotes a relation `R : A → X → Ψ`. Here `X` is the type of its arguments, `Ψ` is the type
of propositions, and `A` holds anything else the relation takes. This file defines three ways to
change the arguments of such a relation.

For `σ : Y → X`, we define `comapArgs σ R a y = R a (σ y)`. This substitutes `σ y` for the
arguments.

For `σ : X → Y` and `Ψ` a complete lattice, we define `mapArgs σ R a y` as the supremum of `R a x`
over all `x` with `σ x = y`. When propositions are sets of worlds, `mapArgs σ R a y` holds exactly
when `R a x` holds for some such `x`. The arguments that `σ` forgets are existentially quantified.
Passive does this to the subject of a verb.

We show that `mapArgs σ` and `comapArgs σ` form a Galois connection (`gc_mapArgs_comapArgs`). It
follows that `mapArgs σ R = ⊥` exactly when `R = ⊥` (`mapArgs_eq_bot`). If `σ` is surjective,
then `mapArgs σ (comapArgs σ R) = R` (`mapArgs_comapArgs`).

When the arguments are tuples `I → E`, we define `mapIndex f R` for a partial map of indices
`f : I → Option J`. The relation `mapIndex f R a y` is the supremum of `R a x` over the tuples `x`
such that `x i = y j` whenever `f i = some j`. An index with `f i = none` is existentially
quantified. Two indices with the same image must have the same value.

We show that `mapIndex` along a total map is `comapArgs` (`mapIndex_some_comp`), and that
`mapIndex` along the partial inverse of an injection is `mapArgs` (`mapIndex_partialInv`).
Applying `mapIndex` twice entails applying it once along the composite (`mapIndex_mapIndex_le`).
The two are equal when no two indices share an image that the second map sends to `none`
(`mapIndex_mapIndex`).

## Implementation notes

* `mapArgs` and `comapArgs` are analogous to `Finsupp.mapDomain` and `Finsupp.comapDomain`, with
  a supremum in place of a sum.
* `mapIndex` requires the value at `j` to equal the value at every `i` with `f i = some j`. This
  is the reading of a reflexive. A reciprocal, where one position holds a group whose members
  are the participants, is not an instance.

## References

* [chierchia-1984]
* [chierchia-1989]
-/

@[expose] public section

open Function

namespace ArgumentStructure

variable {A Ψ W X Y Z : Type*}

/-- The relation `R` with `σ y` substituted for its arguments. -/
def comapArgs (σ : Y → X) (R : A → X → Ψ) : A → Y → Ψ :=
  fun a y ↦ R a (σ y)

@[simp] theorem comapArgs_apply (σ : Y → X) (R : A → X → Ψ) (a : A) (y : Y) :
    comapArgs σ R a y = R a (σ y) :=
  rfl

variable [CompleteLattice Ψ] {R : A → X → Ψ} {σ : X → Y}

/-- The relation that holds of `y` when `R` holds of some `x` with `σ x = y`. The arguments that
`σ` forgets are existentially quantified. -/
def mapArgs (σ : X → Y) (R : A → X → Ψ) : A → Y → Ψ :=
  fun a y ↦ ⨆ x, ⨆ (_ : σ x = y), R a x

theorem gc_mapArgs_comapArgs (σ : X → Y) :
    GaloisConnection (mapArgs σ : (A → X → Ψ) → _) (comapArgs σ) :=
  fun R _ ↦ ⟨fun h a x ↦ (le_iSup₂ (f := fun x' (_ : σ x' = σ x) ↦ R a x') x rfl).trans (h a (σ x)),
    fun h a _ ↦ iSup₂_le fun x hx ↦ hx ▸ h a x⟩

theorem le_mapArgs (σ : X → Y) (R : A → X → Ψ) (a : A) (x : X) : R a x ≤ mapArgs σ R a (σ x) :=
  (gc_mapArgs_comapArgs σ).le_u_l R a x

@[simp] theorem mapArgs_id (R : A → X → Ψ) : mapArgs id R = R := by
  funext a y
  simp [mapArgs]

theorem mapArgs_comp (τ : Y → Z) (σ : X → Y) (R : A → X → Ψ) :
    mapArgs (τ ∘ σ) R = mapArgs τ (mapArgs σ R) :=
  show _ = (mapArgs τ ∘ mapArgs σ) R from (gc_mapArgs_comapArgs (τ ∘ σ)).l_unique
    ((gc_mapArgs_comapArgs σ).compose (gc_mapArgs_comapArgs τ)) fun _ ↦ rfl

@[simp] theorem mapArgs_eq_bot : mapArgs σ R = ⊥ ↔ R = ⊥ :=
  (gc_mapArgs_comapArgs σ).l_eq_bot.trans le_bot_iff

/-- If `σ` is surjective, substituting along `σ` and then quantifying along `σ` gives back the
relation. -/
theorem mapArgs_comapArgs (hσ : Surjective σ) (R : A → Y → Ψ) :
    mapArgs σ (comapArgs σ R) = R := by
  funext a y
  obtain ⟨x, rfl⟩ := hσ y
  exact le_antisymm (iSup₂_le fun x' hx' ↦ (congrArg (R a) hx').le)
    (le_mapArgs σ (comapArgs σ R) a x)

@[simp] theorem mem_mapArgs {R : A → X → Set W} {a : A} {y : Y} {w : W} :
    w ∈ mapArgs σ R a y ↔ ∃ x, σ x = y ∧ w ∈ R a x := by
  simp [mapArgs]

/-! ### Partial maps of the indices of a tuple -/

variable {E I J K : Type*}

/-- The relation that holds of a `J`-tuple `y` when `R` holds of some `I`-tuple `x` with
`x i = y j` whenever `f i = some j`. -/
def mapIndex (f : I → Option J) (R : A → (I → E) → Ψ) : A → (J → E) → Ψ :=
  fun a y ↦ ⨆ x : I → E, ⨆ (_ : ∀ i, ∀ j ∈ f i, x i = y j), R a x

@[simp] theorem mapIndex_some (R : A → (I → E) → Ψ) : mapIndex some R = R := by
  funext a y
  have h : ∀ x : I → E, (∀ i, ∀ j ∈ some i, x i = y j) ↔ x = y := fun x ↦ by simp [funext_iff]
  simp only [mapIndex, h, iSup_iSup_eq_left]

/-- Along a total map of indices, `mapIndex` is `comapArgs`. -/
theorem mapIndex_some_comp (σ : I → J) (R : A → (I → E) → Ψ) :
    mapIndex (some ∘ σ) R = comapArgs (· ∘ σ) R := by
  funext a y
  have h : ∀ x : I → E, (∀ i, ∀ j ∈ (some ∘ σ) i, x i = y j) ↔ x = y ∘ σ :=
    fun x ↦ by simp [funext_iff]
  simp only [mapIndex, h, iSup_iSup_eq_left, comapArgs_apply]

/-- Along the partial inverse of an injection `ι`, `mapIndex` is `mapArgs`. -/
theorem mapIndex_partialInv (ι : J → I) (f : I → Option J)
    (hf : ∀ i j, f i = some j ↔ ι j = i) (R : A → (I → E) → Ψ) :
    mapIndex f R = mapArgs (· ∘ ι) R := by
  funext a y
  have h : ∀ x : I → E, (∀ i, ∀ j ∈ f i, x i = y j) ↔ x ∘ ι = y := fun x ↦
    ⟨fun h ↦ funext fun j ↦ h (ι j) j ((hf _ _).2 rfl), fun h i j hj ↦ by
      rw [← (hf i j).1 hj, ← h]; rfl⟩
  simp only [mapIndex, mapArgs, h]

/-- Applying `mapIndex` twice entails applying it once along the composite map. -/
theorem mapIndex_mapIndex_le (f : I → Option J) (g : J → Option K) (R : A → (I → E) → Ψ) :
    mapIndex g (mapIndex f R) ≤ mapIndex (fun i ↦ (f i).bind g) R := by
  intro a z
  refine iSup₂_le fun y hy ↦ iSup₂_le fun x hx ↦ ?_
  refine le_iSup₂ (f := fun x (_ : ∀ i, ∀ k ∈ (f i).bind g, x i = z k) ↦ R a x) x fun i k hk ↦ ?_
  obtain ⟨j, hj, hk⟩ := Option.bind_eq_some_iff.1 hk
  exact (hx i j hj).trans (hy j k hk)

/-- Applying `mapIndex` twice equals applying it once along the composite, when no two indices
share an image that the second map sends to `none`. -/
theorem mapIndex_mapIndex [Nonempty E] (f : I → Option J) (g : J → Option K)
    (h : ∀ i i' j, f i = some j → f i' = some j → g j = none → i = i')
    (R : A → (I → E) → Ψ) :
    mapIndex g (mapIndex f R) = mapIndex (fun i ↦ (f i).bind g) R := by
  classical
  refine le_antisymm (mapIndex_mapIndex_le f g R) fun a z ↦ iSup₂_le fun x hx ↦ ?_
  let y : J → E := fun j ↦ (g j).elim
    (if hj : ∃ i, f i = some j then x hj.choose else Classical.arbitrary E) z
  have hy : ∀ j, ∀ k ∈ g j, y j = z k := fun j k hk ↦ by
    simp only [y, Option.mem_def.1 hk, Option.elim_some]
  have hxy : ∀ i, ∀ j ∈ f i, x i = y j := fun i j hj ↦ by
    rcases hg : g j with _ | k
    · have hex : ∃ i, f i = some j := ⟨i, hj⟩
      simp only [y, hg, Option.elim_none, hex, ↓reduceDIte]
      rw [h i hex.choose j hj hex.choose_spec hg]
    · simp only [y, hg, Option.elim_some]
      exact hx i k (by simp [Option.mem_def.1 hj, hg])
  exact (le_iSup₂ (f := fun x (_ : ∀ i, ∀ j ∈ f i, x i = y j) ↦ R a x) x hxy).trans
    (le_iSup₂ (f := fun y (_ : ∀ j, ∀ k ∈ g j, y j = z k) ↦ mapIndex f R a y) y hy)

/-- If no two indices share an image, `mapIndex f R = ⊥` exactly when `R = ⊥`. -/
theorem mapIndex_eq_bot [Nonempty E] (f : I → Option J)
    (hf : ∀ i i' j, f i = some j → f i' = some j → i = i') {R : A → (I → E) → Ψ} :
    mapIndex f R = ⊥ ↔ R = ⊥ := by
  classical
  refine ⟨fun h ↦ funext₂ fun a x ↦ le_bot_iff.1 ?_,
    fun h ↦ by subst h; funext a y; simp [mapIndex]⟩
  let y : J → E := fun j ↦ if hj : ∃ i, f i = some j then x hj.choose else Classical.arbitrary E
  have hxy : ∀ i, ∀ j ∈ f i, x i = y j := fun i j hj ↦ by
    have hex : ∃ i, f i = some j := ⟨i, hj⟩
    simp only [y, hex, ↓reduceDIte]
    rw [hf i hex.choose j hj hex.choose_spec]
  exact (le_iSup₂ (f := fun x (_ : ∀ i, ∀ j ∈ f i, x i = y j) ↦ R a x) x hxy).trans
    (congrFun (congrFun h a) y).le

end ArgumentStructure
