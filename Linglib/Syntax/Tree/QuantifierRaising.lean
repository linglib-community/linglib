module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Core.Data.RoseTree.Span
public import Mathlib.Logic.Relation

/-!
# Quantifier Raising

Quantifier Raising moves a constituent to the edge of a tree that contains it, leaving a trace
that a binder of the same index abstracts over, so that the moved constituent combines with the
rest of the tree as its scope. The movement is covert: a tree is pronounced as it stands and
interpreted as one of its logical forms, the trees that steps of raising derive from it, each of
which [has the words of the tree it is derived
from](##PhraseStructure.Tree.IsLogicalForm.yield_perm).
A step may raise from any subtree to that subtree's edge, and steps may be repeated, raise a trace,
or raise what contains one, as in May's and Heim and Kratzer's theories.

## Main definitions

* `PhraseStructure.Tree.bindersAbove`: the indices of the binders dominating a position.
* `PhraseStructure.Tree.raise`, `PhraseStructure.Tree.raiseOf`: the constituent at an address,
  or a given constituent, raised to the edge of the tree.
* `PhraseStructure.Tree.PassesNoIsland`: a constituent crosses no island on its way to the edge.
* `PhraseStructure.Tree.Raises`: one step of raising, within any subtree, under a theory of
  islands.
* `PhraseStructure.Tree.IsLogicalForm`: the trees that raising derives from a tree.

## Implementation notes

`raise` adjoins to the root, the mother an adjunction of the root's category whose host is the
binder. It is total, as `RoseTree.replaceAt` is: an address outside the tree leaves the tree
unchanged. No condition on the index is imposed, so a step may bind a trace it should not. A
landing site is the edge of a subtree, and adjoining there does not leave the subtree: the islands
a step crosses are the subtrees properly between the landing site and the constituent.

## References

* [may-1985]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace PhraseStructure.Tree

variable {C W : Type*}

/-- The indices of the binders that dominate the position `p`, those a trace at `p` could be bound
by. -/
def bindersAbove : Tree C W → List ℕ → Finset ℕ
  | _, [] => ∅
  | RoseTree.node l cs, i :: p =>
    (match l with | Label.bind m _ => {m} | _ => ∅) ∪
      match cs[i]? with
      | some c => bindersAbove c p
      | none => ∅

@[simp] theorem bindersAbove_nil (t : Tree C W) : t.bindersAbove [] = ∅ := by
  cases t; rfl

theorem bindersAbove_bind (m : ℕ) (c : C) (t : Tree C W) (p : List ℕ) :
    (bind m c t).bindersAbove (0 :: p) = insert m (t.bindersAbove p) := by
  simp [bindersAbove]

theorem bindersAbove_phrase {c : C} {k : PhraseKind} {cs : List (Tree C W)} {i : ℕ}
    {t : Tree C W} (h : cs[i]? = some t) (p : List ℕ) :
    (phrase c k cs).bindersAbove (i :: p) = t.bindersAbove p := by
  simp [bindersAbove, h]

/-- Quantifier Raising of the constituent at `p`: it adjoins to the tree, leaving a trace of index
`n` that a binder of the same index abstracts over. -/
def raise (n : ℕ) (p : List ℕ) (t : Tree C W) : Tree C W :=
  match t[p]? with
  | some a => adjoin t.cat [a, bind n t.cat (t.replaceAt p (trace n (Tree.cat a)))]
  | none => t

theorem raise_of_getElem? {t a : Tree C W} {p : List ℕ} (h : t[p]? = some a) (n : ℕ) :
    t.raise n p = adjoin t.cat [a, bind n t.cat (t.replaceAt p (trace n (Tree.cat a)))] := by
  simp [raise, h]

theorem raise_of_getElem?_eq_none {t : Tree C W} {p : List ℕ} (h : t[p]? = none) (n : ℕ) :
    t.raise n p = t := by
  simp [raise, h]

/-- Quantifier Raising of the first occurrence of the constituent `a`. -/
def raiseOf [DecidableEq C] [DecidableEq W] (t : Tree C W) (n : ℕ) (a : Tree C W) : Tree C W :=
  match t.addressOf? a with
  | some p => t.raise n p
  | none => t

theorem raiseOf_of_addressOf? [DecidableEq C] [DecidableEq W] {t a : Tree C W} {p : List ℕ}
    (h : t.addressOf? a = some p) (n : ℕ) : t.raiseOf n a = t.raise n p := by
  simp [raiseOf, h]

/-- Raising permutes the terminals: the raised constituent is fronted and nothing is added or
lost. -/
theorem terminals_raise_perm (n : ℕ) (p : List ℕ) (t : Tree C W) :
    (t.raise n p).terminals.Perm t.terminals := by
  rcases h : t[p]? with _ | a
  · rw [raise_of_getElem?_eq_none h]
  · rw [raise_of_getElem? h, adjoin, terminals_phrase]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, terminals_bind]
    have h₁ := RoseTree.leafList_replaceAt h (trace n (Tree.cat a))
    have h₂ := RoseTree.take_append_leafList_append_drop h
    rw [terminals, terminals, terminals, h₁]
    conv_rhs => rw [← h₂]
    simp only [List.filterMap_append]
    have : (trace n (Tree.cat a) : Tree C W).leafList.filterMap Label.terminal? = [] := rfl
    rw [this, List.append_nil, List.append_assoc]
    exact List.perm_append_comm_assoc _ _ _

theorem yield_raise_perm (n : ℕ) (p : List ℕ) (t : Tree C W) :
    (t.raise n p).yield.Perm t.yield :=
  (terminals_raise_perm n p t).map _

/-! ### Islands

A theory of scope islands is a relation `I`, where `I a b` says that the subtree `b` is an island
for the constituent `a`: islandhood may depend on what moves as well as on what it would leave. A
step of raising is restricted by the islands it would cross, and the unrestricted theory is `⊥`. -/

/-- The constituent at `p` passes no island of `I` on its way to the edge of `t`: no subtree
properly between the root and the constituent is an island for it. -/
def PassesNoIsland (I : Tree C W → Tree C W → Prop) (t : Tree C W) (p : List ℕ) : Prop :=
  ∀ a ∈ t[p]?, ∀ k < p.length, 0 < k → ∀ b ∈ t[p.take k]?, ¬ I a b

instance (I : Tree C W → Tree C W → Prop) [∀ a b, Decidable (I a b)] (t : Tree C W)
    (p : List ℕ) : Decidable (t.PassesNoIsland I p) := by
  unfold PassesNoIsland; infer_instance

@[simp] theorem passesNoIsland_bot (t : Tree C W) (p : List ℕ) : t.PassesNoIsland ⊥ p :=
  fun _ _ _ _ _ _ _ h ↦ h

/-- With more islands, fewer constituents pass. -/
theorem PassesNoIsland.mono {I I' : Tree C W → Tree C W → Prop} (h : I ≤ I') {t : Tree C W}
    {p : List ℕ} (hp : t.PassesNoIsland I' p) : t.PassesNoIsland I p :=
  fun a ha k hk hk' b hb hI ↦ hp a ha k hk hk' b hb (h a b hI)

/-- One step of covert movement under the islands `I`: a constituent of a subtree raises to that
subtree's edge, passing no island. -/
inductive Raises (I : Tree C W → Tree C W → Prop) : Tree C W → Tree C W → Prop
  | intro {t s a : Tree C W} {q p : List ℕ} (n : ℕ) : t[q]? = some s → s[p]? = some a →
      s.PassesNoIsland I p → Raises I t (t.replaceAt q (s.raise n p))

/-- `t'` is a logical form of `t` under the islands `I` when covert movement derives it. -/
def IsLogicalForm (I : Tree C W → Tree C W → Prop) : Tree C W → Tree C W → Prop :=
  Relation.ReflTransGen (Raises I)

variable {I I' : Tree C W → Tree C W → Prop}

/-- Raising to the edge of the whole tree is a step. -/
theorem raises_raise {t a : Tree C W} {p : List ℕ} (h : t[p]? = some a)
    (hI : t.PassesNoIsland I p) (n : ℕ) : Raises I t (t.raise n p) :=
  .intro (q := []) n rfl h hI

theorem Raises.mono (h : I ≤ I') {t t' : Tree C W} (ht : Raises I' t t') : Raises I t t' := by
  cases ht with | intro n hq hp hI => exact .intro n hq hp (hI.mono h)

namespace IsLogicalForm

@[refl] protected theorem refl (t : Tree C W) : IsLogicalForm I t t := Relation.ReflTransGen.refl

@[trans] protected theorem trans {t t' t'' : Tree C W} (h : IsLogicalForm I t t')
    (h' : IsLogicalForm I t' t'') : IsLogicalForm I t t'' :=
  Relation.ReflTransGen.trans h h'

/-- A tree with a constituent raised to its edge is a logical form of it. -/
protected theorem raise {t t' a : Tree C W} {p : List ℕ} (h : IsLogicalForm I t t')
    (ha : t'[p]? = some a) (hI : t'.PassesNoIsland I p) (n : ℕ) :
    IsLogicalForm I t (t'.raise n p) :=
  .tail h (raises_raise ha hI n)

/-- A tree with a given constituent raised to its edge is a logical form of it. -/
protected theorem raiseOf [DecidableEq C] [DecidableEq W] {t t' a : Tree C W} {p : List ℕ}
    (h : IsLogicalForm I t t') (ha : t'.addressOf? a = some p) (hI : t'.PassesNoIsland I p)
    (n : ℕ) : IsLogicalForm I t (t'.raiseOf n a) := by
  rw [raiseOf_of_addressOf? ha]
  exact h.raise (RoseTree.getElem?_of_addressOf? ha) hI n

/-- With more islands, a tree has fewer logical forms. -/
protected theorem mono (h : I ≤ I') {t t' : Tree C W} (ht : IsLogicalForm I' t t') :
    IsLogicalForm I t t' := by
  induction ht with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hr ih => exact Relation.ReflTransGen.tail ih (hr.mono h)

end IsLogicalForm

theorem Raises.isLogicalForm {t t' : Tree C W} (h : Raises I t t') : IsLogicalForm I t t' :=
  .single h

theorem Raises.terminals_perm {t t' : Tree C W} (h : Raises I t t') :
    t'.terminals.Perm t.terminals := by
  cases h with | @intro s a q p n hq hp _ => ?_
  have h₁ := RoseTree.leafList_replaceAt hq (s.raise n p)
  have h₂ := RoseTree.take_append_leafList_append_drop hq
  rw [terminals, terminals, h₁]
  conv_rhs => rw [← h₂]
  simp only [List.filterMap_append]
  exact ((terminals_raise_perm n p s).append_left _).append_right _

/-- A logical form has the words of the tree it is derived from. -/
theorem IsLogicalForm.yield_perm {t t' : Tree C W} (h : IsLogicalForm I t t') :
    t'.yield.Perm t.yield := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact (h.terminals_perm.map _).trans ih

end PhraseStructure.Tree
