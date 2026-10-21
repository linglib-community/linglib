/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Context.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.DeriveFintype

/-!
# Overwriting coordinates of a context

`overwrite s c i` is the context `c` with its coordinates in `s` taken from `i`, the operation by
which a shifty operator replaces coordinates of the context with those of an index of the same
type. An expression *depends on* a set of coordinates when taking the others from another context
leaves it unchanged, as an indexical of a given class depends on one coordinate; after a sequence
of overwrites such an expression reads the context of the last overwrite that took its coordinate.

## Main definitions

* `Context.Coord`: the coordinates of a context.
* `Context.overwrite s c i`: `c` with the coordinates in `s` taken from `i`.
* `Context.DependsOn f s`: `f` depends only on the coordinates in `s`.

## Main results

* `overwrite_overwrite`: overwriting `s` and then `t` from the same context overwrites `s ∪ t`.
* `DependsOn.apply_overwrite_of_subset`, `DependsOn.apply_overwrite_of_disjoint`: an expression
  reads the overwriting context when its coordinates are overwritten, the original one when not.
* `DependsOn.apply_foldl_overwrite`: after a sequence of overwrites an expression depending on one
  coordinate reads the context of the last overwrite that took it.

## References

* [anand-nevins-2004]
* [deal-2020]
-/

@[expose] public section

namespace Kaplan.Context

variable {W E P T α β : Type*}

/-- The coordinates of a context. -/
inductive Coord
  | agent
  | addressee
  | world
  | time
  | position
  deriving DecidableEq, Fintype

/-- The context `c` with the coordinates in `s` overwritten by those of `i`. -/
@[simps]
def overwrite (s : Finset Coord) (c i : Context W E P T) : Context W E P T where
  agent := if .agent ∈ s then i.agent else c.agent
  addressee := if .addressee ∈ s then i.addressee else c.addressee
  world := if .world ∈ s then i.world else c.world
  time := if .time ∈ s then i.time else c.time
  position := if .position ∈ s then i.position else c.position

section overwrite

variable (s t : Finset Coord) (c i : Context W E P T)

@[simp] theorem overwrite_empty : overwrite ∅ c i = c := by ext <;> simp

@[simp] theorem overwrite_univ : overwrite .univ c i = i := by ext <;> simp

@[simp] theorem overwrite_self : overwrite s i i = i := by ext <;> simp

/-- Overwriting `s` and then `t` from the same context overwrites `s ∪ t`. -/
theorem overwrite_overwrite : overwrite t (overwrite s c i) i = overwrite (s ∪ t) c i := by
  ext <;> simp only [overwrite_agent, overwrite_addressee, overwrite_world, overwrite_time,
    overwrite_position, Finset.mem_union] <;> split_ifs <;> simp_all

variable {s t}

theorem overwrite_overwrite_of_subset (h : s ⊆ t) : overwrite s i (overwrite t c i) = i := by
  ext <;> simp only [overwrite_agent, overwrite_addressee, overwrite_world, overwrite_time,
    overwrite_position] <;> split_ifs with h₁ h₂ <;> first | rfl | exact absurd (h h₁) h₂

theorem overwrite_overwrite_of_disjoint (h : Disjoint s t) :
    overwrite s c (overwrite t c i) = c := by
  ext <;> simp only [overwrite_agent, overwrite_addressee, overwrite_world, overwrite_time,
    overwrite_position] <;> split_ifs with h₁ h₂ <;>
    first | rfl | exact absurd h₂ (Finset.disjoint_left.1 h h₁)

end overwrite

/-! ### Dependence on coordinates -/

/-- `f` depends only on the coordinates in `s`: taking the other coordinates from another context
leaves its value unchanged. -/
def DependsOn (f : Context W E P T → α) (s : Finset Coord) : Prop :=
  ∀ c i, f (overwrite s c i) = f i

theorem dependsOn_agent : DependsOn (agent : Context W E P T → E) {.agent} := fun _ _ ↦ by simp

theorem dependsOn_addressee : DependsOn (addressee : Context W E P T → E) {.addressee} :=
  fun _ _ ↦ by simp

theorem dependsOn_world : DependsOn (world : Context W E P T → W) {.world} := fun _ _ ↦ by simp

theorem dependsOn_time : DependsOn (time : Context W E P T → T) {.time} := fun _ _ ↦ by simp

theorem dependsOn_position : DependsOn (position : Context W E P T → P) {.position} :=
  fun _ _ ↦ by simp

namespace DependsOn

variable {f : Context W E P T → α} {g : Context W E P T → β} {s t : Finset Coord}

/-- An expression depending on the coordinates `s` reads the overwriting context when they are all
overwritten. -/
theorem apply_overwrite_of_subset (hf : DependsOn f s) (h : s ⊆ t) (c i : Context W E P T) :
    f (overwrite t c i) = f i := by
  rw [← hf i (overwrite t c i), overwrite_overwrite_of_subset c i h]

/-- An expression depending on the coordinates `s` reads the original context when none of them is
overwritten. -/
theorem apply_overwrite_of_disjoint (hf : DependsOn f s) (h : Disjoint s t)
    (c i : Context W E P T) : f (overwrite t c i) = f c := by
  rw [← hf c (overwrite t c i), overwrite_overwrite_of_disjoint c i h]

theorem mono (hf : DependsOn f s) (h : s ⊆ t) : DependsOn f t :=
  hf.apply_overwrite_of_subset h

theorem comp (hf : DependsOn f s) (u : α → β) : DependsOn (u ∘ f) s :=
  fun c i ↦ congrArg u (hf c i)

theorem prodMk (hf : DependsOn f s) (hg : DependsOn g t) :
    DependsOn (fun c ↦ (f c, g c)) (s ∪ t) := fun c i ↦ by
  simp [(hf.mono Finset.subset_union_left) c i, (hg.mono Finset.subset_union_right) c i]

/-- Local Determination: after overwrites by the pairs `ops`, outermost first, an expression
depending on the coordinate `k` reads the context of the last pair that overwrites `k`, or the
original context if none does. -/
theorem apply_foldl_overwrite {k : Coord} (hf : DependsOn f {k}) (c : Context W E P T)
    (ops : List (Finset Coord × Context W E P T)) :
    f (ops.foldl (fun c p ↦ overwrite p.1 c p.2) c) =
      f (((ops.reverse.find? fun p ↦ k ∈ p.1).map Prod.snd).getD c) := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops p ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.find?_cons]
    by_cases hk : k ∈ p.1
    · simpa [hk] using hf.apply_overwrite_of_subset (Finset.singleton_subset_iff.2 hk) _ _
    · rw [hf.apply_overwrite_of_disjoint (Finset.disjoint_singleton_left.2 hk), ih]
      simp [hk]

end DependsOn

end Kaplan.Context
