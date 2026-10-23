/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
module

public import Linglib.Core.Data.RoseTree.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Multiset.ZeroCons

/-!
# Permutation of rose trees

`RoseTree.Perm t s` says that `t` and `s` agree up to reordering the children of every node. It is
the counterpart for rose trees of `List.Perm`, and `UnorderedTree` is the quotient by it. As for
`List.Perm`, transitivity is a constructor and reflexivity and symmetry are theorems. The relation
is mutually inductive with `PermList`, which is `List.Perm` with elements compared by `Perm` in
place of equality.

## Main declarations

* `RoseTree.Perm`, `RoseTree.PermList`: the mutual permutation relations.
* `RoseTree.isSetoid`: the setoid of which `UnorderedTree` is the quotient.

## Main results

* `RoseTree.permList_iff_rel`: `PermList` is `Multiset.Rel Perm` on the coerced lists, so its
  theory is that of `Multiset.Rel`.
* `RoseTree.perm_node_iff`: two nodes are related exactly when their labels are equal and their
  children are related by `Multiset.Rel Perm`.
-/

@[expose] public section

namespace RoseTree

variable {α : Type*}

mutual
/-- Two rose trees are equal up to reordering the children of every vertex.
Transitivity is a constructor (as in `List.Perm`); reflexivity and symmetry
are theorems. -/
inductive Perm : RoseTree α → RoseTree α → Prop where
  /-- Equal labels over permuted, componentwise-related children. -/
  | node {a : α} {cs ds : List (RoseTree α)} :
      PermList cs ds → Perm (.node a cs) (.node a ds)
  /-- Composition of permutations. -/
  | trans {t s u : RoseTree α} : Perm t s → Perm s u → Perm t u

/-- `List.Perm` with corresponding elements related by `Perm` instead of `Eq`. -/
inductive PermList : List (RoseTree α) → List (RoseTree α) → Prop where
  /-- Empty lists are related. -/
  | nil : PermList [] []
  /-- Related heads over related tails. -/
  | cons {c d : RoseTree α} {cs ds : List (RoseTree α)} :
      Perm c d → PermList cs ds → PermList (c :: cs) (d :: ds)
  /-- Swap the first two elements. -/
  | swap (c d : RoseTree α) (cs : List (RoseTree α)) :
      PermList (d :: c :: cs) (c :: d :: cs)
  /-- Composition of permutations. -/
  | trans {cs ds es : List (RoseTree α)} :
      PermList cs ds → PermList ds es → PermList cs es
end

@[inherit_doc] scoped infixl:50 " ~ " => RoseTree.Perm

/-! ### Equivalence -/

private theorem PermList.refl_of {cs : List (RoseTree α)}
    (h : ∀ c ∈ cs, Perm c c) : PermList cs cs := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    exact .cons (h c List.mem_cons_self) (ih fun c hc ↦ h c (List.mem_cons_of_mem _ hc))

@[refl] theorem Perm.refl (t : RoseTree α) : Perm t t := by
  induction t with
  | node a cs ih => exact .node (PermList.refl_of ih)

@[refl] theorem PermList.refl (cs : List (RoseTree α)) : PermList cs cs :=
  .refl_of fun c _ ↦ Perm.refl c

mutual
@[symm] theorem Perm.symm : ∀ {t s : RoseTree α}, Perm t s → Perm s t
  | _, _, .node h => .node h.symm
  | _, _, .trans h₁ h₂ => .trans h₂.symm h₁.symm

@[symm] theorem PermList.symm : ∀ {cs ds : List (RoseTree α)}, PermList cs ds → PermList ds cs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h.symm hs.symm
  | _, _, .swap c d cs => .swap d c cs
  | _, _, .trans h₁ h₂ => .trans h₂.symm h₁.symm
end

instance : Trans (Perm (α := α)) Perm Perm := ⟨.trans⟩
instance : Trans (PermList (α := α)) PermList PermList := ⟨.trans⟩

instance : IsEquiv (RoseTree α) Perm where
  refl := .refl
  symm _ _ := .symm
  trans _ _ _ := .trans

protected theorem Perm.eqv : Equivalence (Perm (α := α)) :=
  ⟨.refl, .symm, .trans⟩

/-- The setoid of rose trees up to child reordering; the nonplanar quotient is
taken over it. -/
instance isSetoid : Setoid (RoseTree α) := ⟨Perm, Perm.eqv⟩

/-! ### Constructors from list-level data -/

theorem PermList.of_forall₂ {cs ds : List (RoseTree α)}
    (h : List.Forall₂ Perm cs ds) : PermList cs ds := by
  induction h with
  | nil => exact .nil
  | cons hcd _ ih => exact .cons hcd ih

theorem PermList.of_perm {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    PermList cs ds := by
  induction h with
  | nil => exact .nil
  | cons x _ ih => exact .cons (Perm.refl x) ih
  | swap x y l => exact .swap x y l
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem PermList.of_rel {cs ds : List (RoseTree α)}
    (h : Multiset.Rel (Perm (α := α)) ↑cs ↑ds) : PermList cs ds := by
  induction cs generalizing ds with
  | nil => exact .of_perm (Multiset.coe_eq_coe.1 (Multiset.rel_zero_left.1 h).symm)
  | cons c cs ih =>
    obtain ⟨d, ds', hcd, hr, he⟩ := Multiset.rel_cons_left.1 (Multiset.cons_coe c cs ▸ h)
    induction ds' using Quotient.inductionOn
    exact (PermList.cons hcd (ih hr)).trans (.of_perm (Multiset.coe_eq_coe.1 he).symm)

theorem Perm.node_of_perm {a : α} {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    Perm (.node a cs) (.node a ds) :=
  .node (.of_perm h)

theorem Perm.node_of_forall₂ {a : α} {cs ds : List (RoseTree α)}
    (h : List.Forall₂ Perm cs ds) : Perm (.node a cs) (.node a ds) :=
  .node (.of_forall₂ h)

/-! ### The `Multiset.Rel` characterization -/

private theorem PermList.rel : ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
    Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds
  | _, _, .nil => .zero
  | _, _, .cons hcd hs => .cons hcd hs.rel
  | _, _, .swap c d cs => by
    rw [show (↑(d :: c :: cs) : Multiset (RoseTree α)) = ↑(c :: d :: cs) from
      Quot.sound (List.Perm.swap c d cs)]
    exact Multiset.rel_refl_of_refl_on fun t _ ↦ Perm.refl t
  | _, _, .trans h₁ h₂ => .trans _ h₁.rel h₂.rel

theorem permList_iff_rel {cs ds : List (RoseTree α)} :
    PermList cs ds ↔ Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds :=
  ⟨PermList.rel, PermList.of_rel⟩

private theorem Perm.value_children : ∀ {t s : RoseTree α}, Perm t s →
    t.value = s.value ∧ Multiset.Rel Perm (↑t.children : Multiset (RoseTree α)) ↑s.children
  | _, _, .node h => ⟨rfl, h.rel⟩
  | _, _, .trans h₁ h₂ =>
    ⟨h₁.value_children.1.trans h₂.value_children.1,
     .trans _ h₁.value_children.2 h₂.value_children.2⟩

theorem perm_node_iff {a b : α} {cs ds : List (RoseTree α)} :
    Perm (.node a cs) (.node b ds) ↔
      a = b ∧ Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds := by
  refine ⟨fun h ↦ h.value_children, fun ⟨hab, hrel⟩ ↦ hab ▸ ?_⟩
  exact .node (permList_iff_rel.mpr hrel)

theorem Perm.value_eq {t s : RoseTree α} (h : Perm t s) : t.value = s.value :=
  h.value_children.1

theorem Perm.children_rel {t s : RoseTree α} (h : Perm t s) :
    Multiset.Rel Perm (↑t.children : Multiset (RoseTree α)) ↑s.children :=
  h.value_children.2

theorem PermList.length_eq {cs ds : List (RoseTree α)} (h : PermList cs ds) :
    cs.length = ds.length := by
  simpa using Multiset.card_eq_card_of_rel (permList_iff_rel.mp h)

theorem PermList.singleton_inv {c d : RoseTree α} (h : PermList [c] [d]) : Perm c d := by
  obtain ⟨b, hb, hcb⟩ :=
    Multiset.exists_mem_of_rel_of_mem h.rel (Multiset.mem_coe.2 (List.mem_singleton_self c))
  obtain rfl : b = d := by simpa using hb
  exact hcb

/-! ### Functoriality -/

variable {β : Type*}

mutual
/-- `RoseTree.map` preserves `Perm` (cf. `List.Perm.map`). -/
theorem Perm.map (f : α → β) : ∀ {t s : RoseTree α}, Perm t s → Perm (t.map f) (s.map f)
  | _, _, .node h => by
    rw [map_node, map_node]; exact .node (PermList.map f h)
  | _, _, .trans h₁ h₂ => .trans (Perm.map f h₁) (Perm.map f h₂)

/-- `List.map ∘ RoseTree.map` preserves `PermList`. -/
theorem PermList.map (f : α → β) : ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
    PermList (cs.map (RoseTree.map f)) (ds.map (RoseTree.map f))
  | _, _, .nil => .nil
  | _, _, .cons h hs => by
    rw [List.map_cons, List.map_cons]; exact .cons (Perm.map f h) (PermList.map f hs)
  | _, _, .swap c d cs => by
    simp only [List.map_cons]; exact .swap _ _ _
  | _, _, .trans h₁ h₂ => .trans (PermList.map f h₁) (PermList.map f h₂)
end

/-! ### Fold invariance

A `fold` whose algebra is congruent along `Multiset.Rel S` of the folded children
carries `Perm` to `S` (`fold_rel`): the generic dissolver of per-function invariance
inductions, relational so that tree-valued folds descend too. `fold_perm` is the
`S := Eq` case; the counts below are such folds. -/

mutual
theorem fold_rel {S : β → β → Prop} [IsPreorder β S] {g : α → List β → β}
    (hg : ∀ (a : α) {l₁ l₂ : List β}, Multiset.Rel S ↑l₁ ↑l₂ → S (g a l₁) (g a l₂)) :
    ∀ {t s : RoseTree α}, Perm t s → S (fold g t) (fold g s)
  | _, _, .node h => by
    rw [fold_node, fold_node]
    exact hg _ (foldList_rel hg h)
  | _, _, .trans h₁ h₂ => trans_of S (fold_rel hg h₁) (fold_rel hg h₂)

theorem foldList_rel {S : β → β → Prop} [IsPreorder β S] {g : α → List β → β}
    (hg : ∀ (a : α) {l₁ l₂ : List β}, Multiset.Rel S ↑l₁ ↑l₂ → S (g a l₁) (g a l₂)) :
    ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
      Multiset.Rel S ↑(cs.map (fold g)) ↑(ds.map (fold g))
  | _, _, .nil => .zero
  | _, _, .cons h hs => by
    simp only [List.map_cons, ← Multiset.cons_coe]
    exact .cons (fold_rel hg h) (foldList_rel hg hs)
  | _, _, .swap c d cs => by
    simp only [List.map_cons, ← Multiset.cons_coe]
    rw [Multiset.cons_swap]
    exact Multiset.rel_refl_of_refl_on fun _ _ ↦ refl_of S _
  | _, _, .trans h₁ h₂ => .trans S (foldList_rel hg h₁) (foldList_rel hg h₂)
end

theorem fold_perm {g : α → List β → β}
    (hg : ∀ (a : α) (l₁ l₂ : List β), l₁.Perm l₂ → g a l₁ = g a l₂) :
    ∀ {t s : RoseTree α}, Perm t s → fold g t = fold g s :=
  fold_rel fun a {l₁ l₂} h ↦ hg a l₁ l₂ (Multiset.coe_eq_coe.mp (Multiset.rel_eq.mp h))

theorem numNodes_perm {t s : RoseTree α} (h : Perm t s) : t.numNodes = s.numNodes :=
  fold_perm (fun _ _ _ h' ↦ congrArg (· + 1) h'.sum_eq) h

theorem numLeaves_perm {t s : RoseTree α} (h : Perm t s) : t.numLeaves = s.numLeaves :=
  fold_perm (fun _ _ _ h' ↦ congrArg (max 1) h'.sum_eq) h

theorem height_perm {t s : RoseTree α} (h : Perm t s) : t.height = s.height :=
  fold_perm (fun _ _ _ h' ↦ congrArg (· + 1) (h'.foldr_eq 0)) h

theorem arity_perm {t s : RoseTree α} (h : Perm t s) : t.arity = s.arity := by
  simpa [arity] using Multiset.card_eq_card_of_rel h.children_rel

end RoseTree
