/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Context.Basic
public import Linglib.Semantics.Reference.Character.Operator
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Tactic.DeriveFintype

/-!
# Overwriting coordinates of a context

This file defines the operation that overwrites coordinates of a context and the shifty operators
built from it. A context has five coordinates: the agent, the addressee, the world, the time and
the position. Let `s` be a set of coordinates and let `c` and `i` be contexts. The context
`overwrite s c i` has the coordinates in `s` from `i` and the other coordinates from `c`.

For example, `overwrite {agent} c i` is the context `c` with the agent of `i`. The first person
reads the agent, so it has there the value it has at `i`. The word *here* reads the position, so
it has there the value it has at `c`.

Let a character have contexts as its indices. The shifty operator for `s` sends a character `χ` to
the character whose value at a context `c` and an index `i` is the value of `χ` at `overwrite s c i`
and `i`. Under an attitude verb that quantifies over indices, it makes the indexicals that read a
coordinate in `s` denote what the reported context provides.

## Main definitions

* `Context.Coord`: the type of the five coordinates of a context.
* `Context.equivPi`: the bijection between contexts and functions that assign a value to each
  coordinate.
* `Context.overwrite s c i`: the context with the coordinates in `s` from `i` and the other
  coordinates from `c`.
* `Context.Coord.ofRole r`: the coordinate that holds the discourse role `r`.
* `Context.localDepth ss k`: the position, counting from one, of the last set in the list `ss`
  that contains the coordinate `k`, or `0` if no set contains it.
* `Character.shiftyOp s χ`: the character `fun c i ↦ χ (overwrite s c i) i`.

## Main results

* `Context.overwrite_overwrite`: overwriting `s` and then `t` from the same context is
  overwriting `s ∪ t`.
* `Context.apply_overwrite_of_subset`: a function that depends only on coordinates in `t` has the
  same value at `overwrite t c i` as at `i`.
* `Context.apply_overwrite_of_disjoint`: a function that depends on no coordinate in `t` has the
  same value at `overwrite t c i` as at `c`.
* `Context.apply_foldl_overwrite`: after a list of overwrites, a function that depends only on
  the coordinate `k` has the value it has at the context of the last overwrite whose set contains
  `k`. This is Local Determination.
* `Character.shiftyOp_shiftyOp`: the shifty operator for `s` followed by the one for `t` is the
  shifty operator for `t ∪ s`.
* `Character.diag_shiftyOp`: a shifty operator does not change the diagonal of a character along
  the identity.

## Implementation notes

The operation `overwrite` is `Finset.piecewise` on functions of the coordinates, carried to
contexts by `Context.equivPi`. A function on contexts depends only on a set `s` of coordinates if
its composition with the inverse of `Context.equivPi` satisfies `DependsOn` for `s`.

The four type parameters of a context are in one universe, since one function gives the type of
values of each coordinate.

## References

* [anand-nevins-2004]
* [deal-2020]
-/

@[expose] public section

universe u

namespace SpeechAct.Context

variable {W E P T : Type u} {α : Type*}

/-- A **coordinate** of a context is one of its five components: the agent, the addressee, the
world, the time and the position. -/
inductive Coord
  | agent
  | addressee
  | world
  | time
  | position
  deriving DecidableEq, Fintype

/-- The **carrier** of a coordinate is the type of the values the coordinate takes. -/
abbrev Coord.Carrier (W E P T : Type u) : Coord → Type u
  | .agent | .addressee => E
  | .world => W
  | .time => T
  | .position => P

/-- The bijection between contexts and functions that assign to each coordinate a value in its
carrier. -/
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

/-- The context `overwrite s c i` has the coordinates in `s` from the context `i` and the other
coordinates from the context `c`. We say that `c` is **overwritten** on `s` from `i`. -/
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

/-- Overwriting on `s` and then on `t` from the same context is overwriting on `s ∪ t`. -/
theorem overwrite_overwrite : overwrite t (overwrite s c i) i = overwrite (s ∪ t) c i := by
  refine equivPi.injective (funext fun k ↦ ?_)
  simp only [equivPi_overwrite, Finset.piecewise, Finset.mem_union]
  split_ifs <;> tauto

end overwrite

/-! ### The coordinates of the discourse roles -/

/-- The **coordinate of a discourse role** is the agent coordinate for the speaker role and the
addressee coordinate for the addressee role. -/
def Coord.ofRole : SpeechAct.Role ↪ Coord where
  toFun
    | .speaker => .agent
    | .addressee => .addressee
  inj' a b h := by cases a <;> cases b <;> first | rfl | cases h

/-- The holder of a role at `overwrite s c i` is the holder at `i` if `s` contains the coordinate
of the role, and the holder at `c` otherwise. -/
theorem holder_overwrite (s : Finset Coord) (c i : Context W E P T) (r : SpeechAct.Role) :
    (overwrite s c i).holder r = if Coord.ofRole r ∈ s then i.holder r else c.holder r := by
  cases r <;> rfl

/-! ### Expressions reading some coordinates -/

theorem dependsOn_agent :
    DependsOn (agent ∘ equivPi.symm : (Π k, Coord.Carrier W E P T k) → E) {Coord.agent} :=
  fun _ _ h ↦ h _ rfl

variable {f : Context W E P T → α} {s : Set Coord} {t : Finset Coord}

/-- A function that depends only on the coordinates in `s` has the same value at
`overwrite t c i` as at `i` if `s ⊆ t`. -/
theorem apply_overwrite_of_subset (hf : DependsOn (f ∘ equivPi.symm) s) (h : s ⊆ t)
    (c i : Context W E P T) : f (overwrite t c i) = f i := by
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    hf (x := equivPi (overwrite t c i)) (y := equivPi i)
      fun k hk ↦ by simp [Finset.piecewise_eq_of_mem _ _ _ (h hk)]

/-- A function that depends only on the coordinates in `s` has the same value at
`overwrite t c i` as at `c` if `s` and `t` are disjoint. -/
theorem apply_overwrite_of_disjoint (hf : DependsOn (f ∘ equivPi.symm) s) (h : Disjoint s t)
    (c i : Context W E P T) : f (overwrite t c i) = f c := by
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    hf (x := equivPi (overwrite t c i)) (y := equivPi c)
      fun k hk ↦ by simp [Finset.piecewise_eq_of_notMem _ _ _ (Set.disjoint_left.1 h hk)]

/-- A function that depends only on one coordinate has the same value at `overwrite t c i` as at
`c` if it has the same value at `i` as at `c`. -/
theorem apply_overwrite_of_apply_eq {k : Coord} (hf : DependsOn (f ∘ equivPi.symm) {k})
    {c i : Context W E P T} (h : f i = f c) : f (overwrite t c i) = f c := by
  by_cases hk : k ∈ t
  · rw [apply_overwrite_of_subset hf (by simpa using hk), h]
  · exact apply_overwrite_of_disjoint hf (by simpa using hk) c i

/-! ### Local Determination -/

/-- The **local depth** of a coordinate `k` in a list `ss` of sets of coordinates is the position,
counting from one, of the last set in `ss` that contains `k`, or `0` if no set contains it. -/
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

/-- **Local Determination**: let `ops` be a list of pairs of a set of coordinates and a context,
and overwrite a context `c` by each pair in turn. A function that depends only on the coordinate
`k` has, at the result, the value it has at the context of the last pair whose set contains `k`,
or at `c` if no set contains `k`. -/
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

end SpeechAct.Context

namespace Character

open SpeechAct Context

variable {W E P T : Type u} {α : Type*}

/-- The **shifty operator** for a set `s` of coordinates sends a character `χ` to the character
whose value at a context `c` and an index `i` is the value of `χ` at `overwrite s c i` and `i`
([anand-nevins-2004], [deal-2020]). -/
def shiftyOp (s : Finset Coord) :
    Character (Context W E P T) (Context W E P T) α →
      Character (Context W E P T) (Context W E P T) α :=
  shiftBy fun i c ↦ overwrite s c i

variable (s t : Finset Coord) (χ : Character (Context W E P T) (Context W E P T) α)

@[simp] theorem shiftyOp_apply (c i : Context W E P T) :
    shiftyOp s χ c i = χ (overwrite s c i) i := rfl

@[simp] theorem shiftyOp_empty : shiftyOp ∅ χ = χ := by ext; simp

/-- The shifty operator for `s` followed by the shifty operator for `t` is the shifty operator for
`t ∪ s`. -/
@[simp] theorem shiftyOp_shiftyOp : shiftyOp t (shiftyOp s χ) = shiftyOp (t ∪ s) χ := by
  ext; simp [overwrite_overwrite]

/-- A shifty operator does not change the diagonal of a character along the identity: a sentence
that is not embedded has the same value with the operator as without it. -/
theorem diag_shiftyOp : (shiftyOp s χ).diag id = χ.diag id := by
  ext; simp

end Character
