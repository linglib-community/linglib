/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Decidable equality of nonplanar rose trees

Two rose trees represent the same nonplanar tree exactly when they are equal up to
reordering the children of every vertex (`RoseTree.Perm`). This file shows that the
relation is decidable, and computably so: the decision procedure reduces in the kernel,
so concrete `UnorderedTree` equalities close by `decide`.

## Main definitions

- `RoseTree.eqv`: Boolean comparison of two ordered trees up to child reordering — equal
  root values, and child lists matching as multisets under `eqv` (greedy matching).

## Main results

- `RoseTree.eqv_iff_perm`: `eqv` decides `Perm`.
- `RoseTree.instDecidableRelPerm`: the resulting `DecidableRel Perm`.
- `UnorderedTree.instDecidableEq`: decidable equality on the quotient, via
  `Quotient.decidableEq`.

## Implementation notes

`eqv` must recurse structurally for kernel reduction (`decide` needs `brecOn`, not
`WellFounded.fix`), so the greedy matcher is inlined as `eqv.go` rather than passed to a list
function. It finds each match with `findIdx?` and removes it with `eraseIdx`, evaluating `eqv` once
per comparison, where the `contains`-then-`erase` shape of `List.isPerm` would evaluate it twice at
every level of the tree.

`List.isPerm_iff` needs a lawful `BEq` on the whole type. `go_iff` needs `eqv` to compute
`mk`-equality only on the pairs `eqv.go` compares, which is what the inductive hypothesis of
`eqv_iff_perm` provides.

`[UPSTREAM]` candidate.
-/

@[expose] public section

namespace RoseTree

open UnorderedTree

variable {α : Type*} [DecidableEq α] {t s : RoseTree α}

/-! ### Deciding `Perm`: equality up to child reordering -/

/-- `eqv t s` decides whether `t` and `s` are equal up to child reordering
(`eqv_iff_perm`). -/
def eqv : RoseTree α → RoseTree α → Bool
  | .node a cs, .node b ds => decide (a = b) && go cs ds
where
  /-- Greedy matching of child lists, pairing each child of the first list with the first
  `eqv`-related child of the second still unmatched. -/
  go : List (RoseTree α) → List (RoseTree α) → Bool
    | [], ds => ds.isEmpty
    | c :: cs, ds =>
      match ds.findIdx? (eqv c) with
      | some i => go cs (ds.eraseIdx i)
      | none => false

private theorem go_iff : ∀ {cs ds : List (RoseTree α)},
    (∀ c ∈ cs, ∀ d ∈ ds, eqv c d ↔ mk c = mk d) →
      (eqv.go cs ds ↔ (cs.map mk).Perm (ds.map mk))
  | [], ds, _ => by simp [eqv.go]
  | c :: cs, ds, h => by
    rw [eqv.go]
    split
    · next i hi =>
      obtain ⟨hil, hci, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
      have := (List.getElem_cons_eraseIdx_perm hil).map mk
      rw [List.map_cons, ← (h c List.mem_cons_self _ (List.getElem_mem hil)).1 hci] at this
      rw [go_iff fun x hx y hy ↦
        h x (List.mem_cons_of_mem _ hx) y ((List.eraseIdx_sublist _ _).subset hy), List.map_cons,
        ← rel_congr_right this, List.perm_cons]
    · next hi =>
      refine iff_of_false Bool.false_ne_true fun hp ↦ ?_
      obtain ⟨d, hd, hcd⟩ := List.mem_map.1 (hp.subset List.mem_cons_self)
      simpa [(h c List.mem_cons_self d hd).2 hcd.symm] using List.findIdx?_eq_none_iff.1 hi d hd

/-- Two ordered trees are `eqv`-related iff they are equal up to reordering the children of
every vertex. -/
theorem eqv_iff_perm : eqv t s ↔ Perm t s := by
  rw [← mk_eq_mk_iff]
  induction t generalizing s with
  | node a cs ih =>
    obtain ⟨b, ds⟩ := s
    rw [eqv, Bool.and_eq_true, decide_eq_true_eq, mk_node_eq_mk_node_iff, Multiset.coe_eq_coe,
      go_iff fun x hx _ _ ↦ ih x hx]

/-- `Perm` is decided by `eqv`, which reduces in the kernel. -/
instance instDecidableRelPerm : DecidableRel (Perm (α := α)) :=
  fun _ _ ↦ decidable_of_iff _ eqv_iff_perm

instance : DecidableRel ((· ≈ ·) : RoseTree α → RoseTree α → Prop) :=
  instDecidableRelPerm

end RoseTree

namespace UnorderedTree

variable {α : Type*} [DecidableEq α]

/-- Equality of nonplanar trees is decided by `RoseTree.eqv` on representatives
(`Quotient.decidableEq`), so concrete `UnorderedTree` equalities close by `decide`. -/
instance instDecidableEq : DecidableEq (UnorderedTree α) :=
  inferInstanceAs (DecidableEq (Quotient (RoseTree.isSetoid (α := α))))

end UnorderedTree
