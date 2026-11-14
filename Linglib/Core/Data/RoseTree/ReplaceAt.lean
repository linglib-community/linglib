/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
module

public import Linglib.Core.Data.RoseTree.Get

/-!
# Replacement at an address of a rose tree

[`RoseTree.replaceAt`](##RoseTree.replaceAt) puts a tree in place of the subtree at a Gorn
address. The subtree at an address neither above nor below the replaced one
[is unchanged](##RoseTree.getElem?_replaceAt_of_not_prefix), the subtree at an address above it
[has the replacement made inside it](##RoseTree.getElem?_replaceAt_of_prefix), and the replacement
[trades the nodes of the old subtree for those of the new](##RoseTree.numNodes_replaceAt). Its
effect on the frontier is in `RoseTree/Span.lean`.
-/

@[expose] public section

namespace RoseTree

variable {α : Type*}

/-- Replace the subtree at a Gorn address; an address outside the tree leaves it unchanged. -/
def replaceAt : RoseTree α → List ℕ → RoseTree α → RoseTree α
  | _, [], new => new
  | node a cs, i :: p, new => node a (cs.modify i (·.replaceAt p new))

@[simp] theorem replaceAt_nil (t new : RoseTree α) : t.replaceAt [] new = new := by
  cases t; rfl

theorem replaceAt_cons (a : α) (cs : List (RoseTree α)) (i : ℕ) (p : List ℕ)
    (new : RoseTree α) :
    (node a cs).replaceAt (i :: p) new = node a (cs.modify i (·.replaceAt p new)) := rfl

@[simp] theorem children_replaceAt_cons (t : RoseTree α) (i : ℕ) (p : List ℕ)
    (new : RoseTree α) :
    (t.replaceAt (i :: p) new).children = t.children.modify i (·.replaceAt p new) := by
  cases t; rfl

@[simp] theorem value_replaceAt_cons (t : RoseTree α) (i : ℕ) (p : List ℕ) (new : RoseTree α) :
    (t.replaceAt (i :: p) new).value = t.value := by
  cases t; rfl

theorem value_replaceAt {t s : RoseTree α} {p : List ℕ} (h : t[p]? = some s)
    {new : RoseTree α} (hv : new.value = s.value) : (t.replaceAt p new).value = t.value := by
  cases p with
  | nil => rw [replaceAt_nil, hv, Option.some.inj h]
  | cons i p => exact value_replaceAt_cons t i p new

theorem replaceAt_cons_of_getElem? {t c : RoseTree α} {i : ℕ} (hc : t.children[i]? = some c)
    (p : List ℕ) (new : RoseTree α) :
    t.replaceAt (i :: p) new = node t.value (t.children.set i (c.replaceAt p new)) := by
  cases t with
  | node a cs =>
    have : Inhabited (RoseTree α) := ⟨c⟩
    rw [children_node] at hc
    rw [replaceAt_cons, List.modify_eq_set, hc, Option.getD_some, value_node, children_node]

/-- Away from the replaced address, at an address neither above nor below it, the subtree is
unchanged. -/
theorem getElem?_replaceAt_of_not_prefix {t new : RoseTree α} {p q : List ℕ} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : (t.replaceAt p new)[q]? = t[q]? := by
  induction p generalizing t q with
  | nil => exact absurd List.nil_prefix hpq
  | cons i p ih =>
    obtain _ | ⟨j, q⟩ := q
    · exact absurd List.nil_prefix hqp
    obtain ⟨a, cs⟩ := t
    obtain rfl | hij := eq_or_ne i j
    · have h (t : RoseTree α) : (t.replaceAt p new)[q]? = t[q]? :=
        ih (fun h ↦ hpq (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
          (fun h ↦ hqp (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
      cases hc : cs[i]? <;> simp [replaceAt_cons, hc, h]
    · simp [replaceAt_cons, hij]

/-- At an address above the replaced one, the subtree has the replacement inside it. -/
theorem getElem?_replaceAt_of_prefix {t new : RoseTree α} {p q : List ℕ} (hqp : q <+: p) :
    (t.replaceAt p new)[q]? = t[q]?.map (·.replaceAt (p.drop q.length) new) := by
  induction q generalizing t p with
  | nil => simp
  | cons j q ih =>
    obtain _ | ⟨i, p⟩ := p
    · exact absurd hqp (by simp)
    obtain ⟨rfl, h⟩ := List.cons_prefix_cons.mp hqp
    obtain ⟨a, cs⟩ := t
    cases hc : cs[j]? <;> simp [replaceAt_cons, hc, ih h]

theorem getElem?_replaceAt_append {t new : RoseTree α} {p : List ℕ} (hp : t[p]?.isSome)
    (q : List ℕ) : (t.replaceAt p new)[p ++ q]? = new[q]? := by
  rw [getElem?_append, getElem?_replaceAt_of_prefix (List.prefix_refl p)]
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hp
  simp [hs]

/-- Replacing the subtree `s` at an address by `new` trades the nodes of `s` for those of `new`. -/
theorem numNodes_replaceAt {t s : RoseTree α} {p : List ℕ} (h : t[p]? = some s)
    (new : RoseTree α) :
    (t.replaceAt p new).numNodes + s.numNodes = t.numNodes + new.numNodes := by
  induction p generalizing t with
  | nil => rw [replaceAt_nil, Option.some.inj h, Nat.add_comm]
  | cons i p ih =>
    obtain ⟨a, cs⟩ := t
    obtain ⟨c, hc, hcs⟩ := getElem?_cons_eq_some_iff.mp h
    rw [children_node] at hc
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
    have := ih hcs
    rw [replaceAt_cons, List.modify_eq_take_cons_drop hi]
    conv_rhs => rw [← List.take_append_drop i cs, List.drop_eq_getElem_cons hi]
    simp only [numNodes_node, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega

/-- Replacing a subtree by a strictly smaller one shrinks the tree. -/
theorem numNodes_replaceAt_lt {t s : RoseTree α} {p : List ℕ} (h : t[p]? = some s)
    {new : RoseTree α} (hlt : new.numNodes < s.numNodes) :
    (t.replaceAt p new).numNodes < t.numNodes := by
  have := numNodes_replaceAt h new
  omega

end RoseTree
