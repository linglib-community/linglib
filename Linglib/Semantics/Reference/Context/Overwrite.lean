/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Kaplan
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Tactic.DeriveFintype

/-!
# Overwriting coordinates of a context

A context is the function from its coordinates to their values (`Context.equivPi`), and
`overwrite s c i` is `c` with its coordinates in `s` taken from `i`, `Finset.piecewise` through that
equivalence: the operation by which a shifty operator replaces coordinates of the context with those
of an index of the same type. An indexical depends, in the sense of `DependsOn`, on one coordinate;
after a sequence of overwrites it reads the context of the last overwrite that took that coordinate.

## Main definitions

* `Context.Coord`, `Context.equivPi`: the coordinates of a context, and the context as a function
  on them.
* `Context.overwrite s c i`: `c` with the coordinates in `s` taken from `i`.
* `Context.localDepth ss k`: the position of the last of the overwrites `ss` that takes `k`.
* `shiftyOp s`: the shifty operator, evaluating its argument at the context overwritten from the
  index, Kaplan's `shiftBy (overwrite s)`.

## Main results

* `overwrite_overwrite`: overwriting `s` and then `t` from the same context overwrites `s ∪ t`.
* `apply_overwrite_of_subset`, `apply_overwrite_of_disjoint`: an expression reads the overwriting
  context when its coordinates are overwritten, the original one when none is.
* `apply_foldl_overwrite`: Local Determination.
* `shiftyOp_shiftyOp`, `holdsAt_shiftyOp`: stacked shifty operators compose to the one overwriting
  the union of their coordinates, and unembedded a shifty operator is vacuous.

## References

* [anand-nevins-2004]
* [deal-2020]
-/

@[expose] public section

universe u

namespace Kaplan.Context

variable {W E P T : Type u} {α : Type*}

/-- The coordinates of a context. -/
inductive Coord
  | agent
  | addressee
  | world
  | time
  | position
  deriving DecidableEq, Fintype

/-- The values a coordinate takes. -/
abbrev Coord.Carrier (W E P T : Type u) : Coord → Type u
  | .agent | .addressee => E
  | .world => W
  | .time => T
  | .position => P

/-- A context is the function from its coordinates to their values. -/
def equivPi : Context W E P T ≃ Π k, Coord.Carrier W E P T k where
  toFun c
    | .agent => c.agent
    | .addressee => c.addressee
    | .world => c.world
    | .time => c.time
    | .position => c.position
  invFun x := ⟨x .agent, x .addressee, x .world, x .time, x .position⟩
  left_inv _ := rfl
  right_inv x := funext fun k ↦ by cases k <;> rfl

/-- The context `c` with the coordinates in `s` overwritten by those of `i`. -/
def overwrite (s : Finset Coord) (c i : Context W E P T) : Context W E P T :=
  equivPi.symm (s.piecewise (equivPi i) (equivPi c))

section overwrite

variable (s t : Finset Coord) (c i : Context W E P T)

@[simp] theorem equivPi_overwrite :
    equivPi (overwrite s c i) = s.piecewise (equivPi i) (equivPi c) :=
  equivPi.apply_symm_apply _

@[simp] theorem overwrite_agent :
    (overwrite s c i).agent = if .agent ∈ s then i.agent else c.agent := rfl

@[simp] theorem overwrite_addressee :
    (overwrite s c i).addressee = if .addressee ∈ s then i.addressee else c.addressee := rfl

@[simp] theorem overwrite_world :
    (overwrite s c i).world = if .world ∈ s then i.world else c.world := rfl

@[simp] theorem overwrite_time : (overwrite s c i).time = if .time ∈ s then i.time else c.time :=
  rfl

@[simp] theorem overwrite_position :
    (overwrite s c i).position = if .position ∈ s then i.position else c.position := rfl

@[simp] theorem overwrite_empty : overwrite ∅ c i = c := by simp [overwrite]

@[simp] theorem overwrite_univ : overwrite .univ c i = i := by simp [overwrite]

@[simp] theorem overwrite_self : overwrite s i i = i := by simp [overwrite, Finset.piecewise_same]

/-- Overwriting `s` and then `t` from the same context overwrites `s ∪ t`. -/
theorem overwrite_overwrite : overwrite t (overwrite s c i) i = overwrite (s ∪ t) c i := by
  refine equivPi.injective (funext fun k ↦ ?_)
  simp only [equivPi_overwrite, Finset.piecewise, Finset.mem_union]
  split_ifs <;> tauto

end overwrite

/-! ### Expressions reading some coordinates -/

theorem dependsOn_agent :
    DependsOn (agent ∘ equivPi.symm : (Π k, Coord.Carrier W E P T k) → E) {Coord.agent} :=
  fun _ _ h ↦ h _ rfl

variable {f : Context W E P T → α} {s : Set Coord} {t : Finset Coord}

/-- An expression reading only the coordinates `s` reads the overwriting context when they are all
overwritten. -/
theorem apply_overwrite_of_subset (hf : DependsOn (f ∘ equivPi.symm) s) (h : s ⊆ t)
    (c i : Context W E P T) : f (overwrite t c i) = f i := by
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    hf (x := equivPi (overwrite t c i)) (y := equivPi i)
      fun k hk ↦ by simp [Finset.piecewise_eq_of_mem _ _ _ (h hk)]

/-- An expression reading only the coordinates `s` reads the original context when none of them is
overwritten. -/
theorem apply_overwrite_of_disjoint (hf : DependsOn (f ∘ equivPi.symm) s) (h : Disjoint s t)
    (c i : Context W E P T) : f (overwrite t c i) = f c := by
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    hf (x := equivPi (overwrite t c i)) (y := equivPi c)
      fun k hk ↦ by simp [Finset.piecewise_eq_of_notMem _ _ _ (Set.disjoint_left.1 h hk)]

/-- Overwriting from a context that agrees with the original on what an expression reads leaves
the expression's value unchanged. -/
theorem apply_overwrite_of_apply_eq {k : Coord} (hf : DependsOn (f ∘ equivPi.symm) {k})
    {c i : Context W E P T} (h : f i = f c) : f (overwrite t c i) = f c := by
  by_cases hk : k ∈ t
  · rw [apply_overwrite_of_subset hf (by simpa using hk), h]
  · exact apply_overwrite_of_disjoint hf (by simpa using hk) c i

/-! ### Local Determination -/

/-- The position, counting from one, of the last of the overwrites `ss` that takes the coordinate
`k`, or `0` if none does. -/
def localDepth (ss : List (Finset Coord)) (k : Coord) : ℕ :=
  ss.zipIdx.foldl (fun d p ↦ if k ∈ p.1 then p.2 + 1 else d) 0

@[simp] theorem localDepth_nil (k : Coord) : localDepth [] k = 0 := rfl

theorem localDepth_append_singleton (ss : List (Finset Coord)) (s : Finset Coord) (k : Coord) :
    localDepth (ss ++ [s]) k = if k ∈ s then ss.length + 1 else localDepth ss k := by
  simp [localDepth, List.zipIdx_append]

theorem localDepth_le_length (ss : List (Finset Coord)) (k : Coord) :
    localDepth ss k ≤ ss.length := by
  induction ss using List.reverseRecOn with
  | nil => rfl
  | append_singleton ss s ih =>
    rw [localDepth_append_singleton, List.length_append, List.length_singleton]
    split_ifs <;> omega

/-- Local Determination: after overwrites by the pairs `ops`, outermost first, an expression
reading only the coordinate `k` reads the context of the last pair that overwrites `k`, the last of
the first `localDepth` overwriting contexts, or the original context if none does. -/
theorem apply_foldl_overwrite {k : Coord} (hf : DependsOn (f ∘ equivPi.symm) {k})
    (c : Context W E P T) (ops : List (Finset Coord × Context W E P T)) :
    f (ops.foldl (fun c p ↦ overwrite p.1 c p.2) c) =
      f (((ops.map Prod.snd).take (localDepth (ops.map Prod.fst) k)).getLastD c) := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops p ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons,
      List.map_nil, localDepth_append_singleton, List.length_map]
    by_cases hk : k ∈ p.1
    · simp only [hk, ↓reduceIte]
      rw [apply_overwrite_of_subset hf (by simpa using hk), List.take_of_length_le (by simp)]
      simp
    · simp only [hk, ↓reduceIte]
      rw [apply_overwrite_of_disjoint hf (by simpa using hk), ih, List.take_append_of_le_length
        (by simpa using localDepth_le_length (ops.map Prod.fst) k)]

end Kaplan.Context

namespace Kaplan

open Context

variable {W E P T : Type u} {α : Type*}

/-- The shifty operator overwriting the coordinates `s` of the context with those of the index,
`⟦OP α⟧^{c,i} = ⟦α⟧^{overwrite s c i, i}` ([anand-nevins-2004], [deal-2020]). -/
def shiftyOp (s : Finset Coord) :
    Character (Context W E P T) (Context W E P T) α →
      Character (Context W E P T) (Context W E P T) α :=
  shiftBy (overwrite s)

variable (s t : Finset Coord) (χ : Character (Context W E P T) (Context W E P T) α)

@[simp] theorem shiftyOp_apply (c i : Context W E P T) :
    shiftyOp s χ c i = χ (overwrite s c i) i := rfl

@[simp] theorem shiftyOp_empty : shiftyOp ∅ χ = χ := by ext; simp

/-- Stacked shifty operators compose to the one overwriting the union of their coordinates. -/
@[simp] theorem shiftyOp_shiftyOp : shiftyOp t (shiftyOp s χ) = shiftyOp (t ∪ s) χ := by
  ext; simp [overwrite_overwrite]

/-- Unembedded, a shifty operator is vacuous: a sentence holds at a context, taken as its own
index, iff its complement does. -/
theorem holdsAt_shiftyOp (χ : Character (Context W E P T) (Context W E P T) Prop)
    (c : Context W E P T) : (shiftyOp s χ).HoldsAt id c ↔ χ.HoldsAt id c := by
  simp [Character.HoldsAt]

end Kaplan
