/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.Head
public import Linglib.Syntax.Minimalist.Label.SelectionRule
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Token

/-!
# Selection by a stack of categories

This file gives the selection rule in which a head's residue is a stack of categories, consumed
from the top: a head selects a sister when the sister is saturated, its own stack empty, and its
category is the one on top. It is [adger-2003]'s identification of the projecting item with the
selecting item, instantiating the bare-phrase-structure projection ([chomsky-1995-bare] §4) that
[marcolli-chomsky-berwick-2025] §1.13.3 abstracts as head functions (Definition 1.13.6 / Lemma
1.13.7), and [collins-stabler-2016]'s triggered Merge. The selection state of a syntactic object
is then the extension of the states of its leaves, an item with the stack its lexical entry gives
it.

## Main definitions

* `Minimalist.SelectionRule.stack`: the stack rule.
* `Minimalist.SelectionRule.State.IsSaturated`: the head selects nothing further.
* `Minimalist.SyntacticObject.selectionState`: the selection state of a syntactic object, a
  morphism of magmas `SyntacticObject →ₙ* SelectionRule.stack.State`.
* `Minimalist.SyntacticObject.selectionHead`, `Minimalist.SyntacticObject.cat?`: the head token
  by selection and its category.

## Main results

* `Minimalist.SelectionRule.stack_projects_iff`: under the stack rule a constituent projects over
  a sister exactly when it selects it.
* `Minimalist.SelectionRule.State.isSaturated_iff_not_isSaturated_of_mul_ne_zero`,
  `Minimalist.SelectionRule.State.head_mul_of_not_isSaturated`: Merge is triggered, one factor
  selecting and the other saturated, and the selecting factor projects.

## Implementation notes

Two sisters never each select the other under the stack rule, so no head outranks another.
`selectionState` reads only the token's category and `sel`. Two saturated sisters have no head,
as in [marcolli-chomsky-berwick-2025]'s partial head functions: a specifier and its sister are
labeled, if at all, by the labeling algorithm.

## References

* [adger-2003]
* [chomsky-1995-bare]
* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-! ### The stack rule -/

/-- The stack rule: a head whose stack has the category of a saturated sister on top selects it,
and is left with the rest of the stack. -/
def SelectionRule.stack : SelectionRule LexicalItem.Token (List Cat) where
  Selects r b u := r.head? = some b.item.cat ∧ u = []
  rest r _ _ := r.tail

namespace SelectionRule

open State

@[simp] theorem stack_selects_iff {r u : List Cat} {b : LexicalItem.Token} :
    stack.Selects r b u ↔ r.head? = some b.item.cat ∧ u = [] :=
  Iff.rfl

@[simp] theorem stack_rest (r u : List Cat) (b : LexicalItem.Token) : stack.rest r b u = r.tail :=
  rfl

/-- Under the stack rule a constituent projects over a sister exactly when it selects it, since
a selected sister is saturated and selects nothing. -/
theorem stack_projects_iff {x y : stack.Constituent} :
    x.Projects y ↔ x.residue.head? = some y.head.item.cat ∧ y.residue = [] :=
  ⟨And.left, fun h ↦ ⟨h, fun h' ↦ by simp [h.2] at h'⟩⟩

namespace State

variable (x y : stack.State) (a b : LexicalItem.Token) (c : Cat) (r u : List Cat)

theorem stack_of_mul_of :
    (of a r * of b u : stack.State) =
      if r.head? = some b.item.cat ∧ u = [] then of a r.tail
      else if u.head? = some a.item.cat ∧ r = [] then of b u.tail else 0 := by
  rw [of_mul_of]
  simp only [merge, stack_projects_iff]
  rfl

theorem of_cons_mul_of_nil :
    (of a (c :: r) * of b [] : stack.State) = if b.item.cat = c then of a r else 0 := by
  rw [stack_of_mul_of]
  by_cases h : b.item.cat = c
  · simp [h]
  · simp [h, Ne.symm h]

theorem of_nil_mul_of_nil : (of a [] * of b [] : stack.State) = 0 := by
  simp [stack_of_mul_of]

theorem of_cons_mul_of_cons (c' : Cat) :
    (of a (c :: r) * of b (c' :: u) : stack.State) = 0 := by
  simp [stack_of_mul_of]

variable {x y}

theorem head_of_mul_of {a t : LexicalItem.Token} {y : stack.State}
    (h : (of a [] * y).head = some t) : y.head = some t := by
  cases y with
  | zero => simp at h
  | of b u =>
    rw [stack_of_mul_of] at h
    split_ifs at h with h₁ h₂
    · simp at h₁
    · exact h
    · cases h

/-- Where a constituent merges with a saturated one, its own head is the head of the result. -/
theorem head_mul_of_nil {x : stack.State} {a : LexicalItem.Token} (h : x * of a [] ≠ 0) :
    (x * of a []).head = x.head := by
  obtain ⟨t, ht⟩ := exists_head_of_ne_zero h
  rw [ht, head_of_mul_of (mul_comm x _ ▸ ht)]

/-! ### Triggered Merge -/

/-- A selection state is saturated when its head selects nothing further. -/
def IsSaturated (x : stack.State) : Prop := x.residual = some []

instance : DecidablePred IsSaturated :=
  fun x ↦ inferInstanceAs (Decidable (x.residual = some []))

@[simp] theorem isSaturated_of {a : LexicalItem.Token} {r : List Cat} :
    (of a r : stack.State).IsSaturated ↔ r = [] := by
  simp [IsSaturated]

/-- [collins-stabler-2016]'s triggered Merge (Definition 27): of the factors of a defined
selection product exactly one is saturated, the other still selecting. -/
theorem isSaturated_iff_not_isSaturated_of_mul_ne_zero (h : x * y ≠ 0) :
    x.IsSaturated ↔ ¬ y.IsSaturated := by
  cases x with
  | zero => simp at h
  | of a r =>
    cases y with
    | zero => simp at h
    | of b u =>
      rw [stack_of_mul_of] at h
      split_ifs at h with h₁ h₂
      · rcases r with _ | ⟨c, r⟩ <;> simp_all
      · rcases u with _ | ⟨c, u⟩ <;> simp_all
      · exact absurd rfl h

/-- [collins-stabler-2016], Theorem 13: the factor whose selection Merge checks projects. -/
theorem head_mul_of_not_isSaturated (h : x * y ≠ 0) (hx : ¬ x.IsSaturated) :
    (x * y).head = x.head := by
  cases x with
  | zero => simp at h
  | of a r =>
    cases y with
    | zero => simp at h
    | of b u =>
      rw [stack_of_mul_of] at h ⊢
      split_ifs at h ⊢ with h₁ h₂
      · rfl
      · exact absurd (by simpa using h₂.2) hx
      · exact absurd rfl h

end State

end SelectionRule

/-! ### The selection head on `SyntacticObject` -/

variable (s : SyntacticObject TokenLeaf) (tok : LexicalItem.Token)

namespace SyntacticObject

/-- The selection state of a syntactic object, the extension of the selection states of its
leaves as a morphism of magmas: Merge multiplies constituents and selection multiplies their
states. It is the selection instance of [marcolli-chomsky-berwick-2025]'s head functions. -/
def selectionState : SyntacticObject TokenLeaf →ₙ* SelectionRule.stack.State :=
  FreeCommMagma.lift fun tok ↦ .of tok tok.item.sel

/-- The projecting head's lexical item, by c-selection. -/
def selectionHead : Option LexicalItem.Token := (selectionState s).head


/-- The category of the projecting head, `none` at exocentric nodes. -/
def cat? : Option Cat := s.selectionHead.map (·.item.cat)

@[simp] theorem selectionState_leaf :
    selectionState (SyntacticObject.leaf tok) = .of tok tok.item.sel :=
  rfl

@[simp] theorem selectionHead_leaf : (SyntacticObject.leaf tok).selectionHead = some tok := rfl

@[simp] theorem selectionHead_merge_self (x : SyntacticObject TokenLeaf) :
    (merge x x).selectionHead = none := by
  simp [selectionHead, map_mul]

/-- The selection head of a merge is the selection head of a daughter. -/
theorem selectionHead_merge {l r : SyntacticObject TokenLeaf} {t : LexicalItem.Token}
    (h : (merge l r).selectionHead = some t) :
    l.selectionHead = some t ∨ r.selectionHead = some t :=
  SelectionRule.State.head_mul (map_mul selectionState l r ▸ h)

/-- The selection head is a head function. -/
theorem isHeadFunction_selectionHead :
    IsHeadFunction (selectionHead : SyntacticObject TokenLeaf → Option LexicalItem.Token) where
  eq_of_mem_leaf h := by simpa [eq_comm] using h
  mem_or_mem := selectionHead_merge

@[simp] theorem cat?_leaf : (SyntacticObject.leaf tok).cat?
    = some tok.item.cat := rfl

end SyntacticObject


end Minimalist
