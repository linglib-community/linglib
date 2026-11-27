/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Syntax.Spine.Label
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Infix
public import Mathlib.Logic.Relation

/-!
# The hierarchy of a set of spines

This file defines the order on heads that a set of spines determines. A step of a set `S` of spines
is a pair of heads `c` and `d` such that `d` is directly above `c` on some spine of `S`. The
hierarchy of `S` is the reflexive transitive closure of its steps, so that a head `c` is no higher
than a head `d` when steps lead from `c` up to `d`. For the spines `[a, b]` and `[b, c]`, the head
`a` is no higher than `c`. Two heads that the spines of `S` order in both ways are each no higher
than the other.

The hierarchy of `S` is the least reflexive and transitive relation for which every spine of `S` is
a chain. Consequently a map from heads to `ℕ` is monotone for the hierarchy if and only if its
values do not decrease along any spine of `S`, and `c` is no higher than `d` if and only if every
such map `f` has `f c ≤ f d`. Grimshaw's functional value of a head is such a map.

## Main definitions

* `Spine.Step`: `Spine.Step S c d` means that `d` is directly above `c` on some spine of `S`.
* `Spine.steps`: the steps of a list of spines, as a list of pairs.

## Main results

* `Spine.reflTransGen_step_le_iff`: the hierarchy of `S` is the least reflexive and transitive
  relation for which every spine of `S` is a chain.
* `Spine.forall_reflTransGen_step_iff`: a map sends the hierarchy of `S` into a reflexive and
  transitive relation if and only if the image of every spine of `S` is a chain for it.
* `Spine.reflTransGen_step_iff_forall_le`: `c` is no higher than `d` if and only if `f c ≤ f d` for
  every `f : H → ℕ` whose values do not decrease along any spine of `S`.
* `Spine.reflTransGen_step_mono`: a larger set of spines has a larger hierarchy.
* `Spine.reflTransGen_step_singleton_iff`: on a spine without repeated heads, the hierarchy of that
  spine alone is the order of the positions of its heads.
* `Spine.decidableReflTransGenStep`: the hierarchy of a list of spines is decidable.

## Implementation notes

The hierarchy of `S` has no name of its own. It is written `Relation.ReflTransGen (Spine.Step S)`,
so that the lemmas about `Relation.ReflTransGen` apply to it, and two heads that are each no higher
than the other are related by `AntisymmRel`.

An identification of two heads `c` and `d` is expressed by putting both `[c, d]` and `[d, c]` in
the set.

## References

* [grimshaw-2000]
-/

@[expose] public section

namespace Spine

variable {H β : Type*} {S T : Set (Spine H)} {r : H → H → Prop} {c d : H} {s : Spine H}

/-! ### Steps -/

/-- A **step** of a set `S` of spines is a pair of heads `c` and `d` such that `d` is directly
above `c` on some spine of `S`. -/
def Step (S : Set (Spine H)) (c d : H) : Prop := ∃ s ∈ S, [c, d] <:+: s.heads

/-- A relation contains the steps of `S` if and only if every spine of `S` is a chain for it. -/
theorem step_le_iff : Step S ≤ r ↔ ∀ s ∈ S, s.heads.IsChain r := by
  refine ⟨fun h s hs ↦ List.isChain_iff_forall_rel_of_append_cons_cons.2 fun x y l₁ l₂ e ↦
      h _ _ ⟨s, hs, l₁, l₂, by simp [e]⟩, ?_⟩
  rintro h x y ⟨s, hs, l₁, l₂, e⟩
  exact List.isChain_iff_forall_rel_of_append_cons_cons.1 (h s hs) (by simpa using e.symm)

theorem step_mono (h : S ⊆ T) : Step S ≤ Step T := fun _ _ ⟨s, hs, hi⟩ ↦ ⟨s, h hs, hi⟩

/-! ### The hierarchy -/

/-- The hierarchy of `S` is the least reflexive and transitive relation for which every spine of
`S` is a chain. -/
theorem reflTransGen_step_le_iff [Std.Refl r] [IsTrans H r] :
    Relation.ReflTransGen (Step S) ≤ r ↔ ∀ s ∈ S, s.heads.IsChain r :=
  ⟨fun h ↦ step_le_iff.1 fun x y hxy ↦ h x y (.single hxy),
    fun h ↦ Relation.reflTransGen_le_of_le (step_le_iff.2 h)⟩

theorem isChain_reflTransGen_step (hs : s ∈ S) :
    s.heads.IsChain (Relation.ReflTransGen (Step S)) :=
  reflTransGen_step_le_iff.1 le_rfl s hs

theorem pairwise_reflTransGen_step (hs : s ∈ S) :
    s.heads.Pairwise (Relation.ReflTransGen (Step S)) :=
  List.isChain_iff_pairwise.1 (isChain_reflTransGen_step hs)

theorem reflTransGen_step_mono (h : S ⊆ T) :
    Relation.ReflTransGen (Step S) ≤ Relation.ReflTransGen (Step T) :=
  Relation.ReflTransGen.mono (step_mono h)

/-- A map `f` sends the hierarchy of `S` into a reflexive and transitive relation `r` if and only
if the image under `f` of every spine of `S` is a chain for `r`. -/
theorem forall_reflTransGen_step_iff {r : β → β → Prop} [Std.Refl r] [IsTrans β r] {f : H → β} :
    (∀ x y, Relation.ReflTransGen (Step S) x y → r (f x) (f y)) ↔
      ∀ s ∈ S, (s.map f).heads.IsChain r := by
  have : Std.Refl fun x y ↦ r (f x) (f y) := ⟨fun _ ↦ refl _⟩
  have : IsTrans H fun x y ↦ r (f x) (f y) := ⟨fun _ _ _ ↦ _root_.trans⟩
  simp only [heads_map, List.isChain_map]
  exact reflTransGen_step_le_iff (S := S) (r := fun x y ↦ r (f x) (f y))

/-- A head `c` is no higher than a head `d` in the hierarchy of `S` if and only if `f c ≤ f d` for
every `f : H → ℕ` whose values do not decrease along any spine of `S`. -/
theorem reflTransGen_step_iff_forall_le :
    Relation.ReflTransGen (Step S) c d ↔
      ∀ f : H → ℕ, (∀ s ∈ S, (s.map f).heads.IsChain (· ≤ ·)) → f c ≤ f d := by
  classical
  refine ⟨fun h f hf ↦ forall_reflTransGen_step_iff.2 hf c d h, fun h ↦ ?_⟩
  have hc := h (fun x ↦ if Relation.ReflTransGen (Step S) c x then 1 else 0) fun s hs ↦ by
    rw [heads_map, List.isChain_map]
    refine (isChain_reflTransGen_step hs).imp fun x y hxy ↦ ?_
    by_cases hx : Relation.ReflTransGen (Step S) c x
    · simp [hx, hx.trans hxy]
    · simp [hx]
  by_contra hcd
  simp [hcd, Relation.ReflTransGen.refl] at hc

/-! ### A single spine -/

section Singleton

variable [DecidableEq H]

/-- On a spine without repeated heads, the height of a head is monotone for the hierarchy of that
spine. -/
theorem height_le_of_reflTransGen_step (hs : s.heads.Nodup)
    (h : Relation.ReflTransGen (Step {s}) c d) : s.height c ≤ s.height d := by
  refine (forall_reflTransGen_step_iff (f := s.height) (r := (· ≤ ·))).2 (fun t ht ↦ ?_) c d h
  obtain rfl : t = s := ht
  rw [heads_map, List.isChain_map]
  exact List.isChain_iff_getElem.2 fun i _ ↦ by
    simp only [height, hs.idxOf_getElem]
    exact Nat.le_succ i

/-- For heads `c` and `d` of a spine `s` without repeated heads, `c` is no higher than `d` in the
hierarchy of `s` if and only if the height of `c` in `s` is at most the height of `d`. -/
theorem reflTransGen_step_singleton_iff (hs : s.heads.Nodup) (hc : c ∈ s) (hd : d ∈ s) :
    Relation.ReflTransGen (Step {s}) c d ↔ s.height c ≤ s.height d := by
  refine ⟨height_le_of_reflTransGen_step hs, fun h ↦ ?_⟩
  have hc' : s.height c < s.heads.length := List.idxOf_lt_length_iff.2 hc
  have hd' : s.height d < s.heads.length := List.idxOf_lt_length_iff.2 hd
  have ec : s.heads[s.height c] = c := List.getElem_idxOf hc'
  have ed : s.heads[s.height d] = d := List.getElem_idxOf hd'
  obtain hlt | heq := h.lt_or_eq
  · exact ec ▸ ed ▸ List.pairwise_iff_getElem.1
      (pairwise_reflTransGen_step (S := {s}) rfl) _ _ hc' hd' hlt
  · exact (List.idxOf_inj hc).1 heq ▸ .refl

end Singleton

/-! ### Decidability for a list of spines -/

/-- The **steps** of a list of spines are the pairs of a head and the head directly above it on a
spine of the list. -/
def steps (L : List (Spine H)) : List (H × H) := L.flatMap fun s ↦ s.heads.zip s.heads.tail

private theorem pair_infix_iff_mem_zip_tail {x y : H} :
    ∀ {l : List H}, [x, y] <:+: l ↔ (x, y) ∈ l.zip l.tail
  | [] => by simp
  | [_] => by simp [List.infix_cons_iff, List.prefix_cons_iff]
  | z :: w :: l => by
    rw [List.infix_cons_iff, pair_infix_iff_mem_zip_tail (l := w :: l)]
    simp [List.prefix_cons_iff, and_comm]

theorem step_iff_mem_steps {L : List (Spine H)} : Step {s | s ∈ L} c d ↔ (c, d) ∈ steps L := by
  simp [Step, steps, pair_infix_iff_mem_zip_tail]

/-- The hierarchy of a list of spines is decidable, by search along its steps. -/
@[instance_reducible]
def decidableReflTransGenStep [DecidableEq H] (L : List (Spine H)) :
    DecidableRel (Relation.ReflTransGen (Step {s | s ∈ L})) := fun c d ↦
  Relation.ReflTransGen.decidable_of_finite_step
    (fun x ↦ ((steps L).filter (·.1 == x)).map (·.2)) ((steps L).map (·.2))
    (fun x y ↦ by simp [step_iff_mem_steps]) (fun _ _ h ↦ by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact List.mem_map_of_mem (List.mem_filter.1 hp).1) c d

end Spine
