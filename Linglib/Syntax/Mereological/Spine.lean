/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Mereological.Derivation
public import Linglib.Syntax.Spine.Label
public import Mathlib.Data.List.ReduceOption

/-!
# The spine of an object in mereological syntax

This file defines the map from a parthood structure and one of its objects to a `Spine`, the list
of heads a phrase projects. `Spine` is a type shared by the frameworks. For any type of heads it
carries the label of a projection, the extension order in which clause sizes are compared, the
complement and the shell of a head, and the pronunciation of its heads as words; and conditions
on projections, such as being an extended projection, are stated on spines of categories. The map
makes all of this apply to the objects of a parthood structure: a statement about spines is a
statement about an object through its spine, and about its categories through the image of that
spine under the map from objects to categories.

In mereological syntax the first dimension of parthood is the extended-projection complement
relation: in a finite clause `V` is the 1-part of `v`, `v` of `T`, and `T` of `C`. The spine of an
object `y` in a parthood structure `P` lists the 1-parts of `y` from the lowest upward, and then
`y`, so the spine of that `C` is `[V, v, T, C]`. An object has at most one immediate 1-part, so
its 1-parts form a chain and the list is determined. A spine depends on parthood in the first
dimension only: adding a 2-part, a specifier, changes no spine.

The map carries the structure of parthood to the structure of spines. The spine of `x` lies below
the spine of `y` exactly when `x` is `y` or a 1-part of `y`, so the extension order on spines is
parthood in the first dimension, and a structure with more parts has larger spines. Subjoin acts
on spines in one way. An object that is not yet a part and subjoins as the 1-part of `y` becomes
the complement of `y`: the spine of `y` is then that object's spine with `y` on top. Every other
licensed subjunction leaves every spine as it was. In particular a part that subjoins does so as
a 2-part, so movement extends no projection. It follows that the spine of an object that is a
part, or has a 1-part, is the same in every structure derived from there: a complement is
complete before a head is built over it.

## Main definitions

* `Parthood.spine`: the spine of an object.
* `Parthood.spineHom`: the spine of an object as an order homomorphism of structures.

## Main results

* `Parthood.mem_spine_iff`: the heads of the spine of `y` are `y` and its 1-parts.
* `Parthood.Subjoins.spine_of_nextDim_one`: subjoining `x` as the 1-part of `y` appends `y` to
  the spine of `x`.
* `Parthood.Subjoins.spine_of_isPart`: a part that subjoins changes no spine.
* `Parthood.Derives.spine_eq`: derivations do not change the spine of an object that is a part
  or has a 1-part.
* `Parthood.spine_le_spine_iff`: the extension order on spines is parthood in the first
  dimension.

## Implementation notes

The spine of `y` is computed by following `P.part .one` from `y` for as many steps as there are
objects, so that it is evaluated by `decide`. In a structure with a cycle of 1-parts through `y`
this list repeats; `mem_spine_iff` holds there too, and the equations for a spine take
acyclicity as a hypothesis.

## References

* [adger-2025]
-/

@[expose] public section

namespace MereologicalSyntax.Parthood

open Relation Function

variable {α : Type*} {P Q : Parthood α} {x y z : α}

private theorem nPart_one_iff_transGen :
    P.NPart .one x y ↔ TransGen (fun a b ↦ b ∈ P.part .one a) y x :=
  transGen_swap.symm

private theorem iterate_bind_eq_of_forall
    (h : ∀ w, (w = z ∨ P.NPart .one w z) → Q.part .one w = P.part .one w) (n : ℕ) :
    (·.bind (Q.part .one))^[n] (some z) = (·.bind (P.part .one))^[n] (some z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    rcases hw : (·.bind (P.part .one))^[n] (some z) with _ | w
    · rw [hw]
      rfl
    · rw [hw]
      refine h w ?_
      cases n with
      | zero => exact .inl (Option.some_injective _ hw).symm
      | succ n =>
        exact .inr (nPart_one_iff_transGen.2 (transGen_iff_exists_iterate.2 ⟨n, hw⟩))

private theorem reduceOption_iterate_some (n : ℕ) :
    (List.iterate (·.bind (P.part .one)) (some y) (n + 1)).reduceOption =
      y :: (List.iterate (·.bind (P.part .one)) (P.part .one y) n).reduceOption :=
  rfl

private theorem reduceOption_iterate_none (n : ℕ) :
    (List.iterate (·.bind (P.part .one)) none n).reduceOption = [] := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

variable [Fintype α]

variable (P) in
/-- The spine of `y`: the 1-parts of `y` from the lowest upward, and then `y`. -/
def spine (y : α) : Spine α :=
  ⟨(List.iterate (·.bind (P.part .one)) (some y)
    (Fintype.card (Option α) + 1)).reduceOption.reverse⟩

theorem mem_spine_iff : x ∈ P.spine y ↔ x = y ∨ P.NPart .one x y := by
  rw [nPart_one_iff_transGen, transGen_iff_mem_iterate, Spine.mem_def, spine, List.mem_reverse,
    reduceOption_iterate_some, List.mem_cons, List.reduceOption_mem_iff]

theorem self_mem_spine (y : α) : y ∈ P.spine y := mem_spine_iff.2 (.inl rfl)

/-- The spine of `z` depends only on the immediate 1-parts of `z` and of its 1-parts. -/
theorem spine_congr (h : ∀ w ∈ P.spine z, Q.part .one w = P.part .one w) :
    Q.spine z = P.spine z := by
  have h' := iterate_bind_eq_of_forall fun w hw ↦ h w (mem_spine_iff.2 hw)
  simp only [spine, ← List.range_map_iterate, h']

theorem spine_of_part_eq_none (h : P.part .one y = none) : P.spine y = ⟨[y]⟩ := by
  rw [spine, reduceOption_iterate_some, h, reduceOption_iterate_none]
  rfl

private theorem iterate_card_eq_none (hP : P.Acyclic) (y : α) :
    (·.bind (P.part .one))^[Fintype.card (Option α)] (some y) = none := by
  by_contra hne
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨m, hm, hmw⟩ := exists_lt_card_iterate_eq hw
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hm
  rw [hk, show m + k + 1 = (k + 1) + m by omega, iterate_add_apply, hmw, iterate_succ_apply] at hw
  exact hP.not_nPart_self (nPart_one_iff_transGen.2 (transGen_iff_exists_iterate.2 ⟨k, hw⟩))

/-- In an acyclic structure, the spine of an object is that object over the spine of its
immediate 1-part. -/
theorem Acyclic.spine_of_imm (hP : P.Acyclic) (h : P.Imm .one x y) :
    P.spine y = (P.spine x).append [y] := by
  have hx : (List.iterate (·.bind (P.part .one)) (some x)
        (Fintype.card (Option α) + 1)).reduceOption =
      (List.iterate (·.bind (P.part .one)) (some x) (Fintype.card (Option α))).reduceOption := by
    rw [List.iterate_add, List.reduceOption_append, iterate_card_eq_none hP x]
    exact List.append_nil _
  rw [spine, spine, hx, reduceOption_iterate_some, show P.part .one y = some x from h,
    Spine.append, List.reverse_cons]

/-! ### The order -/

section Order

variable [DecidableEq α]

/-- The spine of `x` lies below the spine of `y` exactly when `x` is `y` or a 1-part of `y`. -/
theorem spine_le_spine_iff : P.spine x ≤ P.spine y ↔ x = y ∨ P.NPart .one x y := by
  refine ⟨fun h ↦ mem_spine_iff.1 (Spine.le_iff_forall_mem.1 h x (self_mem_spine x)),
    fun h ↦ Spine.le_iff_forall_mem.2 fun c hc ↦ mem_spine_iff.2 ?_⟩
  rcases mem_spine_iff.1 hc with rfl | hcx
  · exact h
  · exact h.elim (fun e ↦ .inr (e ▸ hcx)) fun hxy ↦ .inr (hcx.trans hxy)

theorem spine_mono (y : α) : Monotone fun P : Parthood α ↦ P.spine y := fun _ _ h ↦
  Spine.le_iff_forall_mem.2 fun _ hc ↦
    mem_spine_iff.2 ((mem_spine_iff.1 hc).imp_right (·.mono h))

/-- The spine of an object, as an order homomorphism of structures. -/
def spineHom (y : α) : Parthood α →o Spine α := ⟨fun P ↦ P.spine y, spine_mono y⟩

@[simp] theorem spineHom_apply (y : α) (P : Parthood α) : spineHom y P = P.spine y := rfl

/-! ### Subjoin -/

/-- Adding a 2-part, a specifier, changes no spine. -/
theorem spine_addPart_two (P : Parthood α) (x y z : α) :
    (P.addPart .two x y).spine z = P.spine z :=
  spine_congr fun w _ ↦ by simp [part_addPart]

namespace Subjoins

/-- A part that subjoins changes no spine: it subjoins as a 2-part, so movement extends no
projection. -/
theorem spine_of_isPart (h : P.Subjoins x y Q) (hx : P.IsPart x) (z : α) :
    Q.spine z = P.spine z := by
  obtain ⟨n, hn, rfl⟩ := subjoin_eq_some_iff.1 h.subjoin_eq
  obtain rfl := nextDim_eq_two (isSome_part_one_of_canSubjoin (h.canSubjoin hx)) hn
  exact spine_addPart_two ..

theorem spine_of_isSome (h : P.Subjoins x y Q) (hy : (P.part .one y).isSome) (z : α) :
    Q.spine z = P.spine z := by
  obtain ⟨n, hn, rfl⟩ := subjoin_eq_some_iff.1 h.subjoin_eq
  obtain rfl := nextDim_eq_two hy hn
  exact spine_addPart_two ..

theorem spine_of_ne (h : P.Subjoins x y Q) (hz : z ≠ y) : Q.spine z = P.spine z := by
  by_cases hx : P.IsPart x
  · exact h.spine_of_isPart hx z
  obtain ⟨n, -, rfl⟩ := subjoin_eq_some_iff.1 h.subjoin_eq
  refine spine_congr fun w hw ↦ ?_
  have hwy : w ≠ y := by
    rintro rfl
    rcases mem_spine_iff.1 hw with rfl | hwz
    · exact hz rfl
    · exact h.extension hx (descendant_of_nPart hwz).isPart
  simp [part_addPart, hwy]

/-- Subjoining `x` as the 1-part of `y` appends `y` to the spine of `x`: `y` takes `x` as its
complement. -/
theorem spine_of_nextDim_one (h : P.Subjoins x y Q) (hP : P.Acyclic)
    (hn : P.nextDim y = some .one) : Q.spine y = (P.spine x).append [y] := by
  obtain ⟨n, hn', hQ⟩ := h.imm_iff
  obtain rfl : n = .one := Option.some_injective _ (hn'.symm.trans hn)
  rw [(h.acyclic hP).spine_of_imm ((hQ _ _ _).2 (.inr ⟨rfl, rfl, rfl⟩)), h.spine_of_ne h.ne]

/-- A licensed subjunction does not change the spine of an object that is a part or has a
1-part. -/
theorem spine_eq (h : P.Subjoins x y Q) (hz : P.IsPart z ∨ (P.part .one z).isSome) :
    Q.spine z = P.spine z := by
  by_cases hzy : z = y
  · subst hzy
    by_cases hx : P.IsPart x
    · exact h.spine_of_isPart hx z
    · exact h.spine_of_isSome (hz.resolve_left (h.extension hx)) z
  · exact h.spine_of_ne hzy

end Subjoins

/-- Derivations do not change the spine of an object that is a part or has a 1-part: a spine is
complete before anything is built over it. -/
theorem Derives.spine_eq (h : P.Derives Q) (hz : P.IsPart z ∨ (P.part .one z).isSome) :
    Q.spine z = P.spine z := by
  induction h with
  | refl => rfl
  | tail hPR hRQ ih =>
    obtain ⟨_, _, hRQ⟩ := hRQ
    have hle := Derives.le hPR
    rw [hRQ.spine_eq (hz.imp (·.mono hle) fun hs ↦ ?_), ih]
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
    exact Option.isSome_iff_exists.2 ⟨w, Imm.mono hle hw⟩

end Order

end MereologicalSyntax.Parthood
