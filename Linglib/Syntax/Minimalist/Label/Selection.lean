/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.SelectionState
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Selection by a stack of categories

This file gives the selection discipline in which a head's residue is a stack of categories,
consumed from the top: a head selects a sister when the sister is saturated, its own stack
empty, and its category is the one on top. It is [adger-2003]'s identification of the projecting
item with the selecting item, instantiating the bare-phrase-structure projection
([chomsky-1995-bare] §4) that [marcolli-chomsky-berwick-2025] §1.13.3 abstracts as head functions
(Definition 1.13.6 / Lemma 1.13.7), and [collins-stabler-2016]'s triggered Merge. The selection
state of a syntactic object is then the extension of the states of its leaves, an item with the
stack its lexical entry gives it.

## Main definitions

* `Selection SelStack`: the stack discipline.
* `Minimalist.SelectionState.IsSaturated`: the head selects nothing further.
* `Minimalist.SyntacticObject.selCheck`: the selection state of a syntactic object.
* `Minimalist.SyntacticObject.selHead`, `Minimalist.SyntacticObject.cat?`:
  the head token and its category.
* `Minimalist.SyntacticObject.selCheckHom`: `selCheck` as a morphism of magmas
  `SyntacticObject →ₙ* SelectionState SelStack`, the extension of the leaves' states.

## Main results

* `Minimalist.SyntacticObject.selHead_map`: a relabelling that preserves selection commutes
  with the selection-driven head.
* `Minimalist.SelectionState.isSaturated_iff_not_isSaturated_of_mul_ne_zero`,
  `Minimalist.SelectionState.head_mul_of_not_isSaturated`: Merge is triggered, one factor
  selecting and the other saturated, and the selecting factor projects.

## Implementation notes

Two sisters never each select the other under the stack discipline, so no head outranks another.
The trace of a token is a lower copy of the phrase it heads, so it gets that phrase's value,
saturated with the token's category (`traceState`), and a head that selected the moved phrase
still selects its trace; the bare trace remembers no token and gets the saturated dummy
`.of .bareTrace []`. `selCheck` reads only the token's category and `sel`. Two saturated sisters
have no head, as in [marcolli-chomsky-berwick-2025]'s partial head functions: a specifier and its
sister are labeled, if at all, by the labeling algorithm (`Label/MinimalSearch.lean`).

## References

* [adger-2003]
* [chomsky-1995-bare]
* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-! ### The stack discipline -/

/-- A head whose stack has the category `c` on top selects a saturated sister of category `c`,
and is left with the rest of the stack. -/
instance : Selection SelStack where
  select
    | c :: rest, b, [] => if b.item.cat = c then some rest else none
    | _, _, _ => none

@[simp] theorem select_cons_nil (c : Cat) (rest : SelStack) (b : LexicalItem.Token) :
    Selection.select (c :: rest) b ([] : SelStack) = if b.item.cat = c then some rest else none :=
  rfl

@[simp] theorem select_nil (b : LexicalItem.Token) (u : SelStack) :
    Selection.select ([] : SelStack) b u = none := rfl

@[simp] theorem select_cons (r : SelStack) (b : LexicalItem.Token) (c : Cat) (u : SelStack) :
    Selection.select r b (c :: u) = none := by
  cases r <;> rfl

variable (x y : SelectionState SelStack)

section

variable (ha hb : LexicalItem.Token) (c c' : Cat) (rest rest' : SelStack)

theorem selCombine_cons_nil :
    selCombine (⟨some (ha, c :: rest)⟩ : SelectionState SelStack) ⟨some (hb, [])⟩ =
      if hb.item.cat = c then some (true, ha, rest) else none := by
  simp only [selCombine, select_cons_nil, select_nil]
  split_ifs <;> rfl

theorem selCombine_nil_cons :
    selCombine (⟨some (ha, [])⟩ : SelectionState SelStack) ⟨some (hb, c :: rest)⟩ =
      if ha.item.cat = c then some (false, hb, rest) else none := by
  simp only [selCombine, select_cons_nil, select_nil]
  split_ifs <;> rfl

theorem selCombine_nil_nil :
    selCombine (⟨some (ha, [])⟩ : SelectionState SelStack) ⟨some (hb, [])⟩ = none := rfl

theorem selCombine_cons_cons :
    selCombine (⟨some (ha, c :: rest)⟩ : SelectionState SelStack) ⟨some (hb, c' :: rest')⟩ =
      none := rfl

end

/-- A relabelling that keeps each token's category commutes with the product. -/
theorem SelectionState.map_mul_of_preservesSelection {f : LexicalItem.Token → LexicalItem.Token}
    (hf : LexicalItem.Token.PreservesSelection f) : (x * y).map f = x.map f * y.map f :=
  SelectionState.map_mul (f := f)
    (fun r b u ↦ by
      rcases r with _ | ⟨c, r⟩ <;> rcases u with _ | ⟨c', u⟩ <;>
        simp [hf.cat])
    (fun _ _ ↦ Iff.rfl) x y

/-- Exocentricity is a zero divisor, since two saturated nonzero states multiply to `0`. -/
example : ∃ x y : SelectionState SelStack, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 :=
  ⟨.of .bareTrace [], .of .bareTrace [], by decide⟩

variable {x y}

theorem SelectionState.head_of_mul_of {a r : LexicalItem.Token} {y : SelectionState SelStack}
    (h : (SelectionState.of a [] * y).head = some r) : y.head = some r := by
  rcases y with ⟨_ | ⟨hb, _ | ⟨c, rest⟩⟩⟩
  · cases h
  · cases h
  · simp only [SelectionState.mul_def, SelectionState.of, selCombine_nil_cons] at h
    split_ifs at h <;> simp_all [SelectionState.head]

/-! ### Triggered Merge -/

/-- A selection state is saturated when its head selects nothing further. -/
def SelectionState.IsSaturated (x : SelectionState SelStack) : Prop := x.residual = some []

instance : DecidablePred SelectionState.IsSaturated :=
  fun x ↦ inferInstanceAs (Decidable (x.residual = some []))

/-- [collins-stabler-2016]'s triggered Merge (Definition 27): of the factors of a defined
selection product exactly one is saturated, the other still selecting. -/
theorem SelectionState.isSaturated_iff_not_isSaturated_of_mul_ne_zero (h : x * y ≠ 0) :
    x.IsSaturated ↔ ¬ y.IsSaturated := by
  rcases x with ⟨_ | ⟨hx, _ | ⟨cx, sx⟩⟩⟩ <;> rcases y with ⟨_ | ⟨hy, _ | ⟨cy, sy⟩⟩⟩ <;>
    first
    | exact absurd rfl h
    | simp [SelectionState.IsSaturated, SelectionState.residual]

/-- [collins-stabler-2016], Theorem 13: the factor whose selection Merge checks projects. -/
theorem SelectionState.head_mul_of_not_isSaturated (h : x * y ≠ 0) (hx : ¬ x.IsSaturated) :
    (x * y).head = x.head := by
  rcases x with ⟨_ | ⟨a, _ | ⟨c, rest⟩⟩⟩ <;> rcases y with ⟨_ | ⟨b, _ | ⟨c', rest'⟩⟩⟩ <;>
    try first
    | exact absurd rfl h
    | exact absurd rfl hx
  by_cases hc : b.item.cat = c
  · simp [SelectionState.mul_def, selCombine_cons_nil, hc, SelectionState.head]
  · exact absurd (by simp [SelectionState.mul_def, selCombine_cons_nil, hc]; rfl) h

/-! ### Selection check on the carriers -/

/-- The selection state of a trace is a saturated copy of the phrase its token heads, and for the
    bare trace the saturated dummy. -/
def traceState : Option LexicalItem.Token → SelectionState SelStack
  | some tok => .of tok []
  | none => .of .bareTrace []

/-! ### The selection-driven head on `SyntacticObject` -/

variable (s : SyntacticObject) (tok : LexicalItem.Token)

namespace SyntacticObject

/-- The selection check as a morphism of magmas, the extension of the selection states of the
leaves: Merge multiplies constituents and selection multiplies their states. -/
def selCheckHom : SyntacticObject →ₙ* SelectionState SelStack :=
  FreeCommMagma.lift (Leaf.elim (fun tok ↦ .of tok tok.item.sel) traceState)

/-- **Selection-driven head check**: the selection instance of
    [marcolli-chomsky-berwick-2025]'s head functions; computable. -/
def selCheck : SelectionState SelStack := selCheckHom s

/-- The projecting head's lexical item, by c-selection. -/
def selHead : Option LexicalItem.Token := s.selCheck.head


/-- The category of the projecting head, `none` at exocentric nodes. -/
def cat? : Option Cat := s.selHead.map (·.item.cat)

@[simp] theorem selCheck_leaf : (SyntacticObject.leaf tok).selCheck
    = .of tok tok.item.sel := rfl

@[simp] theorem selCheck_trace : trace.selCheck = .of .bareTrace [] := rfl

@[simp] theorem selCheck_traceOf : (traceOf tok).selCheck = .of tok [] := rfl

@[simp] theorem selCheck_node (l r : SyntacticObject) :
    (merge l r).selCheck = l.selCheck * r.selCheck := map_mul selCheckHom l r

@[simp] theorem selCheckHom_apply : selCheckHom s = s.selCheck := rfl

@[simp] theorem selHead_leaf : (SyntacticObject.leaf tok).selHead = some tok := rfl

@[simp] theorem selHead_merge_self (x : SyntacticObject) : (merge x x).selHead = none := by
  simp [selHead]

variable {f : LexicalItem.Token → LexicalItem.Token}

theorem selCheck_map (hf : LexicalItem.Token.PreservesSelection f) :
    (s.map f).selCheck = s.selCheck.map f := by
  induction s using ind with
  | leaf a => simp [SelectionState.map, SelectionState.of, hf.sel]
  | trace => simp [SelectionState.map, SelectionState.of, hf.bareTrace]
  | traceOf a => simp [SelectionState.map, SelectionState.of]
  | merge l r ihl ihr => rw [map_merge, selCheck_node, selCheck_node, ihl, ihr,
      SelectionState.map_mul_of_preservesSelection _ _ hf]

theorem selHead_map (hf : LexicalItem.Token.PreservesSelection f) :
    (s.map f).selHead = s.selHead.map f := by
  rw [selHead, selHead, selCheck_map s hf, SelectionState.head_map]

@[simp] theorem cat?_leaf : (SyntacticObject.leaf tok).cat?
    = some tok.item.cat := rfl

end SyntacticObject

/-- The selection state of a tree, that of the syntactic object it is the tree of, and `0` on a
tree that is not well formed. -/
def selCheckN (t : UnorderedTree Vertex) : SelectionState SelStack :=
  if h : IsSyntacticObject t then (SyntacticObject.ofUnorderedTree t h).selCheck else 0

@[simp] theorem selCheckN_toUnorderedTree (s : SyntacticObject) :
    selCheckN s.toUnorderedTree = s.selCheck := by
  rw [selCheckN, dite_eq_left s.isSyntacticObject_toUnorderedTree,
    SyntacticObject.ofUnorderedTree_toUnorderedTree]


theorem LexicalItem.Token.PreservesSelection.swap {a b : LexicalItem.Token}
    (hc : a.item.cat = b.item.cat) (hs : a.item.sel = b.item.sel) (ha : a ≠ .bareTrace)
    (hb : b ≠ .bareTrace) : LexicalItem.Token.PreservesSelection (Equiv.swap a b) where
  cat t := by rw [Equiv.swap_apply_def]; split_ifs <;> subst_vars <;> simp [hc]
  sel t := by rw [Equiv.swap_apply_def]; split_ifs <;> subst_vars <;> simp [hs]
  bareTrace := Equiv.swap_apply_of_ne_of_ne ha.symm hb.symm

end Minimalist
