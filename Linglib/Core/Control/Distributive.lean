/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Set.Prod

/-!
# Distributive functors

A functor `M` is distributive when every family of computations indexed by a type `ι` gives one
computation of a family, `distribute : (ι → M α) → M (ι → α)`: the functor distributes over the
function type, as an applicative functor distributes over a list in McBride and Paterson's
`dist`. Function types are not traversable, since not every applicative functor distributes
over them (McBride and Paterson's example is `Option` over functions from the integers), so
distribution is a property of the functor. The identity functor distributes by doing nothing,
the set functor by choosing a value at every index, `Set.pi`, and a reader over a distributive
functor by distributing at each environment.

A distributive functor preserves constant families when a family that computes the same `m` at
every index distributes to the constant functions of the values of `m`. The identity does. The set
functor does not: from a set with two values it distributes the constant family to every function
into that set, not only the constant ones.

## Main definitions

* `Distributive`: the distribution of a functor over function types.
* `Distributive.PreservesConst`: constant families distribute to constant functions.

## Main results

* `Distributive.preservesConst_id`, `Distributive.PreservesConst.readerT`: the identity functor
  preserves constant families, and so does a reader over a functor that does.
* `SetM.mem_run_distribute`: the set functor distributes a family to its choice functions.
* `SetM.not_preservesConst`: the set functor does not preserve constant families.

## References

* [mcbride-paterson-2008]
-/

@[expose] public section

universe u v

/-- A functor distributes over function types when a family of computations indexed by `ι`
gives a computation of families. -/
class Distributive (M : Type u → Type v) where
  /-- The computation of the family of values of a family of computations. -/
  distribute {ι α : Type u} : (ι → M α) → M (ι → α)

export Distributive (distribute)

namespace Distributive

/-- A distributive functor preserves constant families when the family computing `m` at every
index distributes to the constant functions of the values of `m`. -/
def PreservesConst (M : Type u → Type v) [Functor M] [Distributive M] : Prop :=
  ∀ (ι α : Type u) (m : M α), distribute (fun _ : ι ↦ m) = Function.const ι <$> m

instance : Distributive Id.{u} where
  distribute f := f

@[simp] theorem distribute_id {ι α : Type u} (f : ι → Id α) : (distribute f : Id (ι → α)) = f :=
  rfl

theorem preservesConst_id : PreservesConst Id.{u} := fun _ _ _ ↦ rfl

end Distributive

namespace ReaderT

variable {ρ : Type u} {m : Type u → Type v}

/-- A reader over a distributive functor distributes by distributing at each environment. -/
instance [Distributive m] : Distributive (ReaderT ρ m) where
  distribute f r := distribute fun i ↦ f i r

@[simp] theorem run_distribute [Distributive m] {ι α : Type u} (f : ι → ReaderT ρ m α) (r : ρ) :
    (distribute f).run r = distribute fun i ↦ (f i).run r :=
  rfl

/-- A reader over a functor that preserves constant families preserves them too. -/
theorem _root_.Distributive.PreservesConst.readerT [Monad m] [Distributive m]
    (h : Distributive.PreservesConst m) : Distributive.PreservesConst (ReaderT ρ m) :=
  fun ι α x ↦ funext fun r ↦ h ι α (x r)

end ReaderT

namespace SetM

/-- The set functor distributes a family of sets to its choice functions. -/
instance : Distributive SetM.{u} where
  distribute f := Set.pi Set.univ f

@[simp] theorem mem_run_distribute {ι α : Type u} {f : ι → SetM α} {g : ι → α} :
    g ∈ (distribute f).run ↔ ∀ i, g i ∈ (f i).run :=
  Set.mem_univ_pi

theorem run_pure {α : Type u} (a : α) : (pure a : SetM α).run = {a} :=
  rfl

theorem run_map {α β : Type u} (f : α → β) (m : SetM α) : (f <$> m).run = f '' m.run :=
  rfl

theorem run_seq {α β : Type u} (f : SetM (α → β)) (m : SetM α) :
    (f <*> m).run = Set.seq f.run m.run :=
  rfl

/-- The set functor does not preserve constant families: from the set of both truth values it
distributes the constant family to every function, the identity among them, not only to the two
constant functions. -/
theorem not_preservesConst : ¬ Distributive.PreservesConst SetM.{u} := fun h ↦ by
  let B := ULift.{u} Bool
  have hid : (fun x ↦ x) ∈ (distribute (M := SetM) fun _ : B ↦ Set.univ).run :=
    mem_run_distribute.2 fun _ ↦ Set.mem_univ _
  rw [h B B Set.univ, run_map] at hid
  obtain ⟨b, -, hb⟩ := hid
  have h₁ := congrFun hb (ULift.up true)
  have h₂ := congrFun hb (ULift.up false)
  simp only [Function.const_apply] at h₁ h₂
  exact Bool.noConfusion (congrArg ULift.down (h₁.symm.trans h₂))

end SetM
