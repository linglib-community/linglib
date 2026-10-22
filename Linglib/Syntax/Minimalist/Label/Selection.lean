/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Linglib.Syntax.Minimalist.Label.Head
public import Linglib.Syntax.Minimalist.SyntacticObject.Lift

/-!
# Selection-driven heads on the `SyntacticObject` carrier

This file defines the c-selection head of a syntactic object: whichever sister's
head selects the saturated other projects — [adger-2003]'s identification of the
projecting item with the selecting item, instantiating the bare-phrase-structure
projection ([chomsky-1995-bare] §4) that [marcolli-chomsky-berwick-2025] §1.13.3
abstracts as head functions (Definition 1.13.6 / Lemma 1.13.7). Like the book's
head functions it is partial: `0` at exocentric nodes.

## Main declarations

* `Minimalist.SelectionState`: a constituent's selection state — the projecting
  head with its residual selectional stack; a `CommMagma` and `MulZeroClass`, with
  `0` the off-`Dom(h)` failure.
* `Mul SelectionState` and `Minimalist.selSide`: the carrier-free combinators —
  the selection product, and which daughter projects.
* `Minimalist.selNode`, `Minimalist.selCheckPlanar`,
  `Minimalist.SyntacticObject.selCheck`: the selection algebra
  (`SyntacticObject.mergeAlgebra`), its catamorphism, and the carrier lift.
* `Minimalist.SyntacticObject.selHead`, `Minimalist.SyntacticObject.cat?`:
  the head token and its category, the head function of the phases
  (`SyntacticObject.IsPhaseHead`).
* `Minimalist.SyntacticObject.selCheckHom`: `selCheck` as a morphism of magmas
  `SyntacticObject →ₙ* SelectionState`, via `SyntacticObject.lift`.

## Main results

* `mul_comm` (via `CommMagma SelectionState`) and `Minimalist.selSide_comm`:
  order-independence — the formal content of Merge's unordered output.
* `Head SelectionState`: the head of a selection product is a factor's head, so `selHead` is
  endocentric (`Minimalist.mem_head_or_mem_head_of_mem_head_map_mul`).
* `Minimalist.SelectionState.isSaturated_iff_not_isSaturated_of_mul_ne_zero`,
  `Minimalist.SelectionState.head_mul_of_not_isSaturated`: Merge is triggered, one factor
  selecting and the other saturated, and the selecting factor projects.

## Implementation notes

`SelectionState` is a one-field structure over `Option (LexicalItem.Token × List Cat)`, so that the
selection product can be an instance on it: the `Option` is implementation, and `0` is the
public spelling of the exocentric failure, the off-domain value of a partial head function.
There is no `One`, since two saturated states multiply to `0`, and no associativity claim, so the
structure is `CommMagma` + `MulZeroClass` only. The trace of a token is a lower copy of the
phrase it heads, so it gets that phrase's value, saturated with the token's category
(`traceState`), and a head that selected the moved phrase still selects its trace; the bare
trace remembers no token and gets the saturated dummy `.of .bareTrace []`. `selCheck`
reads only the token's category and `sel`. Two saturated sisters have no head, as in
[marcolli-chomsky-berwick-2025]'s partial head functions: a specifier and its sister are
labeled, if at all, by the labeling algorithm (`Label/MinimalSearch.lean`).

## References

* [adger-2003]
* [chomsky-1995-bare]
* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-! ### The selection state -/

/-- A constituent's selection state is the projecting head with its residual stack
    (`.of tok []` = saturated), and `0` off the endocentric domain. -/
structure SelectionState : Type where
  toOption : Option (LexicalItem.Token × List Cat)
deriving DecidableEq

/-- A defined selection state has projecting head `tok` and residual stack `stack`. -/
def SelectionState.of (tok : LexicalItem.Token) (stack : List Cat) : SelectionState :=
  ⟨some (tok, stack)⟩

instance : Zero SelectionState := ⟨⟨none⟩⟩

/-- The projecting head token; `none` off the endocentric domain. -/
def SelectionState.head (x : SelectionState) : Option LexicalItem.Token := x.toOption.map (·.1)

/-- The residual selectional stack (`some []` = saturated). -/
def SelectionState.residual (x : SelectionState) : Option (List Cat) := x.toOption.map (·.2)

@[simp] theorem SelectionState.head_of (tok : LexicalItem.Token) (stack : List Cat) :
    (SelectionState.of tok stack).head = some tok := rfl

@[simp] theorem SelectionState.head_zero : (0 : SelectionState).head = none := rfl

/-! ### Carrier-free selection combinators -/

variable (x y : SelectionState)

/-- The selection decision at a binary node — (which sister projects, head,
    residual), `none` at exocentric nodes; `*` and `selSide` are its projections. -/
def selCombine : SelectionState → SelectionState → Option (Bool × LexicalItem.Token × List Cat)
  | ⟨some (ha, c :: rest)⟩, ⟨some (hb, [])⟩ =>
      if hb.item.cat = c then some (true, ha, rest) else none
  | ⟨some (ha, [])⟩, ⟨some (hb, c :: rest)⟩ =>
      if ha.item.cat = c then some (false, hb, rest) else none
  | _, _ => none

/-- The projecting daughter is reported as `some true` for the left and `some false` for the
    right. -/
def selSide (x y : SelectionState) : Option Bool := (selCombine x y).map (·.1)

/-- Swapping the sisters flips the side and keeps the head and residual. -/
theorem selCombine_comm : selCombine x y = (selCombine y x).map fun p => (!p.1, p.2) := by
  rcases x with ⟨_ | ⟨hx, _ | ⟨cx, sx⟩⟩⟩ <;> rcases y with ⟨_ | ⟨hy, _ | ⟨cy, sy⟩⟩⟩ <;>
    first
    | rfl
    | (simp only [selCombine, Option.map]; split <;> rfl)

/-- S₂-equivariance: swap acts on the sisters, `Bool.not` on the side — MCB's
    per-vertex edge-marking (Lemma 1.13.4). -/
theorem selSide_comm : selSide x y = (selSide y x).map Bool.not := by
  simp only [selSide, selCombine_comm x y, Option.map_map]; rfl

/-- The selection product is the head-and-residual of the `selCombine` decision
    ([marcolli-chomsky-berwick-2025] §1.13); `0` is absorbing. -/
instance : MulZeroClass SelectionState where
  mul x y := ⟨(selCombine x y).map (·.2)⟩
  zero := ⟨none⟩
  zero_mul _ := rfl
  mul_zero x := by rcases x with ⟨_ | ⟨h, _ | ⟨c, s⟩⟩⟩ <;> rfl

/-- `*` unfolds to the canonical accessor for the selection product. -/
theorem SelectionState.mul_def : x * y = ⟨(selCombine x y).map (·.2)⟩ := rfl

instance : CommMagma SelectionState where
  mul_comm x y := by
    simp only [SelectionState.mul_def, selCombine_comm x y, Option.map_map]; rfl

/-- Exocentricity is a zero divisor, since two saturated nonzero states multiply to `0`. -/
example : ∃ x y : SelectionState, x ≠ 0 ∧ y ≠ 0 ∧ x * y = 0 :=
  ⟨.of .bareTrace [], .of .bareTrace [], by decide⟩

/-- A state never combines with itself, since of two equal sisters neither selects the other. -/
@[simp] theorem SelectionState.mul_self (x : SelectionState) : x * x = 0 := by
  rcases x with ⟨_ | ⟨h, _ | ⟨c, s⟩⟩⟩ <;> rfl

variable {x y}

/-- The projected head is the head of the sister on the reported side. -/
theorem selCombine_eq_some {b : Bool} {hd : LexicalItem.Token} {res : List Cat}
    (h : selCombine x y = some (b, hd, res)) :
    (bif b then x else y).head = some hd := by
  match x, y with
  | ⟨some (ha, c :: rest')⟩, ⟨some (hb, [])⟩
  | ⟨some (ha, [])⟩, ⟨some (hb, c :: rest')⟩ =>
    simp only [selCombine] at h
    split_ifs at h; cases h; rfl
  | ⟨some (_, [])⟩, ⟨some (_, [])⟩ | ⟨some (_, _ :: _)⟩, ⟨some (_, _ :: _)⟩
  | ⟨none⟩, _ | ⟨some _⟩, ⟨none⟩ => simp [selCombine] at h

/-- The head of a selection product is one of its factors' heads. -/
instance : Head SelectionState where
  head := SelectionState.head
  head_zero := rfl
  mem_head_or_mem_head_of_mem_head_mul {x y r} h := by
    simp only [Option.mem_def, SelectionState.mul_def, SelectionState.head, Option.map_map,
      Option.map_eq_some_iff] at h
    obtain ⟨⟨b, _, _⟩, hproj, rfl⟩ := h
    cases b
    exacts [Or.inr (selCombine_eq_some hproj), Or.inl (selCombine_eq_some hproj)]

/-- A saturated state never projects, so the head of its product is the other factor's head. -/
theorem SelectionState.head_of_mul_of {a r : LexicalItem.Token} {y : SelectionState}
    (h : (SelectionState.of a [] * y).head = some r) : y.head = some r := by
  rcases y with ⟨_ | ⟨hb, _ | ⟨c, rest⟩⟩⟩
  · cases h
  · cases h
  · simp only [SelectionState.mul_def, SelectionState.of, selCombine] at h
    split_ifs at h <;> simp_all [SelectionState.head]

/-! ### Triggered Merge -/

/-- A selection state is saturated when its head selects nothing further. -/
def SelectionState.IsSaturated (x : SelectionState) : Prop := x.residual = some []

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
  · simp [SelectionState.mul_def, selCombine, hc, SelectionState.head]
  · exact absurd (by simp [SelectionState.mul_def, selCombine, hc]; rfl) h

/-! ### Selection check on the carriers -/

/-- The selection state of a trace is a saturated copy of the phrase its token heads, and for the
    bare trace the saturated dummy. -/
def traceState : Option LexicalItem.Token → SelectionState
  | some tok => .of tok []
  | none => .of .bareTrace []

/-- The selection algebra is the `SyntacticObject.mergeAlgebra` of token + `sel`
    leaves and the traces' `traceState`. -/
def selNode : Vertex → List SelectionState → SelectionState :=
  mergeAlgebra (fun tok => .of tok tok.item.sel) traceState

/-- `selNode` is invariant under permutation of the daughter states. -/
theorem selNode_perm (a : Vertex) {l₁ l₂ : List SelectionState} (h : l₁.Perm l₂) :
    selNode a l₁ = selNode a l₂ :=
  mergeAlgebra_perm _ _ a h

/-- The selection check on a planar tree is the catamorphism of `selNode`. -/
def selCheckPlanar : RoseTree Vertex → SelectionState :=
  RoseTree.fold selNode

/-- At a node, `selCheckPlanar` folds the algebra over the daughters. -/
theorem selCheckPlanar_node (a : Vertex) (cs : List (RoseTree Vertex)) :
    selCheckPlanar (RoseTree.node a cs) = selNode a (cs.map selCheckPlanar) :=
  RoseTree.fold_node ..

/-- `selCheckPlanar` is `Perm`-invariant, so it descends to the quotient. -/
theorem selCheckPlanar_perm {t s : RoseTree Vertex} (h : RoseTree.Perm t s) :
    selCheckPlanar t = selCheckPlanar s :=
  RoseTree.fold_perm (fun a _ _ h' => selNode_perm a h') h

/-- Selection check on the nonplanar carrier. -/
def selCheckN : UnorderedTree Vertex → SelectionState :=
  liftN (fun tok => .of tok tok.item.sel) traceState

@[simp] theorem selCheckN_mk (p : RoseTree Vertex) :
    selCheckN (UnorderedTree.mk p) = selCheckPlanar p := rfl

theorem selCheckN_node (a b : UnorderedTree Vertex) :
    selCheckN (UnorderedTree.node Vertex.bare {a, b}) = selCheckN a * selCheckN b :=
  liftN_merge _ _ a b

/-! ### The selection-driven head on `SyntacticObject` -/

variable (s : SyntacticObject) (tok : LexicalItem.Token)

namespace SyntacticObject

/-- **Selection-driven head check**: the selection instance of
    [marcolli-chomsky-berwick-2025]'s head functions; computable. -/
def selCheck : SelectionState := selCheckN s.val

/-- The projecting head's lexical item, by c-selection. -/
def selHead : Option LexicalItem.Token := s.selCheck.head

/-- Residual pending selectional features (`some []` = saturated). -/
def checkedSel : Option (List Cat) := s.selCheck.residual

/-- The category of the projecting head, `none` at exocentric nodes. -/
def cat? : Option Cat := s.selHead.map (·.item.cat)

@[simp] theorem selCheck_leaf : (SyntacticObject.leaf tok).selCheck
    = .of tok tok.item.sel := rfl

@[simp] theorem selCheck_trace : trace.selCheck = .of .bareTrace [] := rfl

@[simp] theorem selCheck_traceOf : (traceOf tok).selCheck = .of tok [] := rfl

@[simp] theorem selCheck_node (l r : SyntacticObject) :
    (merge l r).selCheck = l.selCheck * r.selCheck := liftFun_merge _ _ l r

/-- `selCheck` as a morphism of magmas ([marcolli-chomsky-berwick-2025] §1.13's
    algebraic frame): the `lift` of the leaf data. -/
noncomputable def selCheckHom : SyntacticObject →ₙ* SelectionState :=
  lift (fun tok => .of tok tok.item.sel) traceState

@[simp] theorem selCheckHom_apply : selCheckHom s = s.selCheck := rfl

@[simp] theorem selHead_leaf : (SyntacticObject.leaf tok).selHead = some tok := rfl

/-- An object merged with itself has no head. -/
@[simp] theorem selHead_merge_self (x : SyntacticObject) : (merge x x).selHead = none := by
  simp [selHead]

@[simp] theorem cat?_leaf : (SyntacticObject.leaf tok).cat?
    = some tok.item.cat := rfl

end SyntacticObject

end Minimalist
