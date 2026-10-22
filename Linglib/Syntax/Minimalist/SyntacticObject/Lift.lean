/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.List.Perm.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# The universal property of the syntactic-object carrier

Leaf data valued in a commutative magma with zero extends to a morphism of magmas
out of `SyntacticObject L` (`lift`, the `FreeMagma.lift` analogue), and two such
morphisms agreeing on the leaves are equal (`hom_ext`). The zero absorbs the
off-carrier arities, so one total algebra (`mergeAlgebra`) drives the fold, the
quotient descent, and the subtype restriction once and for all: consumers supply a
lexical-leaf value and a trace value, the latter for the bare trace (`none`) and for the trace
of each token (`some tok`), the three kinds of leaf `hom_ext` distinguishes, and inherit
`Perm`-invariance from `mul_comm` via a private permutation-invariance lemma — no bespoke step
induction.

## Main declarations

* `Minimalist.SyntacticObject.mergeAlgebra`: the node algebra induced by a
  magma-with-zero — lexical leaf ↦ `ℓ`, trace leaf ↦ `τ` of its token if any, bare binary node
  ↦ `*`, other arities ↦ `0`.
* `Minimalist.SyntacticObject.liftN`: its evaluation on the nonplanar carrier.
* `Minimalist.SyntacticObject.liftFun`, `Minimalist.SyntacticObject.lift`: the
  induced map on syntactic objects, unbundled (computable) and as `→ₙ*`.

## Main results

* `Minimalist.SyntacticObject.hom_ext`: morphisms of magmas out of
  `SyntacticObject L` agreeing on lexical and trace leaves are equal.
* `Minimalist.SyntacticObject.liftN_merge`: the magma law on the unordered carrier.
-/

@[expose] public section

namespace Minimalist.SyntacticObject

variable {L : Type}

open RoseTree UnorderedTree

variable {β : Type*}

/-- The node algebra of a magma-with-zero: lexical leaf ↦ `ℓ`, trace leaf ↦ `τ` of the token it
    is the trace of, if any, bare binary node ↦ `*`, off-carrier arities ↦ `0`. -/
def mergeAlgebra [Mul β] [Zero β] (ℓ : L → β) (τ : Option L → β) :
    Vertex L → List β → β
  | .inl (some tok), _ => ℓ tok
  | .inl none, [x, y]  => x * y
  | .inl none, _       => 0
  | .inr u, []         => τ u
  | .inr _, _          => 0

/-- The trace of a token is a leaf: any daughters put it off the carrier. -/
private theorem mergeAlgebra_some [Mul β] [Zero β] (ℓ : L → β)
    (τ : Option L → β) (tok : L) (l : List β) :
    mergeAlgebra ℓ τ (Sum.inr (some tok)) l = if l.isEmpty then τ (some tok) else 0 := by
  match l with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => rfl

/-- The index-free trace is a leaf: any daughters put it off the carrier. -/
private theorem mergeAlgebra_none [Mul β] [Zero β] (ℓ : L → β)
    (τ : Option L → β)
    (l : List β) : mergeAlgebra ℓ τ (Sum.inr none) l = if l.isEmpty then τ none else 0 := by
  match l with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => rfl

/-- A daughter list of three or more is off the carrier. -/
private theorem mergeAlgebra_big [Mul β] [Zero β] {ℓ : L → β}
    {τ : Option L → β}
    {l : List β}
    (h : 2 < l.length) : mergeAlgebra ℓ τ Vertex.bare l = 0 := by
  match l with
  | _ :: _ :: _ :: _ => rfl
  | [] | [_] | [_, _] => simp at h

/-- A list function symmetric on pairs and constant above length two is `Perm`-invariant:
lengths at most one are rigid under permutation, pairs by the symmetry, longer lists by the
constancy. -/
private theorem perm_congr_arity₂ {β γ : Type*} {g : List β → γ} {c : γ}
    (hswap : ∀ x y, g [x, y] = g [y, x])
    (hbig : ∀ l : List β, 2 < l.length → g l = c)
    {l₁ l₂ : List β} (h : l₁.Perm l₂) : g l₁ = g l₂ := by
  induction h with
  | nil => rfl
  | @cons x l₁ l₂ h _ih =>
    match l₁, l₂, h with
    | [], l₂, h => rw [show l₂ = [] from h.symm.eq_nil]
    | [y], l₂, h => rw [show l₂ = [y] from List.perm_singleton.mp h.symm]
    | _ :: _ :: _, l₂, h =>
      have hl := h.length_eq
      rw [hbig _ (by simp +arith), hbig _ (by simp only [List.length_cons] at hl ⊢; omega)]
  | swap x y l =>
    match l with
    | [] => exact hswap y x
    | _ :: _ => rw [hbig _ (by simp +arith), hbig _ (by simp +arith)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

section CommMagma

variable [CommMagma β] [Zero β] (ℓ : L → β) (τ : Option L → β)

/-- `mergeAlgebra` is invariant under permutation of the daughter values: only the
    binary shape is order-sensitive, and there `mul_comm` applies. -/
theorem mergeAlgebra_perm (a : Vertex L) {l₁ l₂ : List β} (h : l₁.Perm l₂) :
    mergeAlgebra ℓ τ a l₁ = mergeAlgebra ℓ τ a l₂ := by
  cases a with
  | inl o =>
    cases o with
    | some tok => rfl
    | none =>
      exact perm_congr_arity₂ (fun x y => _root_.mul_comm x y) (fun _ h => mergeAlgebra_big h) h
  | inr u =>
    cases u with
    | none =>
      simp only [mergeAlgebra_none, List.isEmpty_iff_length_eq_zero, h.length_eq]
    | some tok =>
      simp only [mergeAlgebra_some, List.isEmpty_iff_length_eq_zero, h.length_eq]

/-- The catamorphism descends to the nonplanar carrier by `mergeAlgebra_perm`, giving the
    induced algebra. -/
def liftN : UnorderedTree (Vertex L) → β :=
  Quotient.lift (RoseTree.fold (mergeAlgebra ℓ τ))
    fun _ _ h => RoseTree.fold_perm (fun a _ _ h' => mergeAlgebra_perm ℓ τ a h') h

@[simp] theorem liftN_mk (p : RoseTree (Vertex L)) :
    liftN ℓ τ (UnorderedTree.mk p) = RoseTree.fold (mergeAlgebra ℓ τ) p := rfl

/-- Merge multiplies values, the nonplanar magma law. -/
theorem liftN_merge (a b : UnorderedTree (Vertex L)) :
    liftN ℓ τ (UnorderedTree.node Vertex.bare {a, b}) = liftN ℓ τ a * liftN ℓ τ b := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  rw [UnorderedTree.quot_mk_eq_mk, UnorderedTree.quot_mk_eq_mk, UnorderedTree.node_pair_mk]
  exact rfl

/-- The induced map on syntactic objects, unbundled — computable, `decide`-friendly. -/
def liftFun (s : SyntacticObject L) : β := liftN ℓ τ s.val

@[simp] theorem liftFun_leaf (tok : L) :
    liftFun ℓ τ (SyntacticObject.leaf tok) = ℓ tok :=
  rfl

@[simp] theorem liftFun_trace : liftFun ℓ τ trace = τ none := rfl

@[simp] theorem liftFun_traceOf (tok : L) :
    liftFun ℓ τ (traceOf tok) = τ (some tok) := rfl

@[simp] theorem liftFun_merge (l r : SyntacticObject L) :
    liftFun ℓ τ (merge l r) = liftFun ℓ τ l * liftFun ℓ τ r := by
  show liftN ℓ τ (merge l r).val = liftN ℓ τ l.val * liftN ℓ τ r.val
  rw [merge_val, liftN_merge]

/-- Leaf data extends to a morphism of magmas out of the carrier, the existence half of the
    universal property (cf. `FreeMagma.lift`). -/
noncomputable def lift : SyntacticObject L →ₙ* β where
  toFun := liftFun ℓ τ
  map_mul' := liftFun_merge ℓ τ

@[simp] theorem lift_apply (s : SyntacticObject L) : lift ℓ τ s = liftFun ℓ τ s := rfl

end CommMagma

/-- Morphisms agreeing on the leaves are equal, the uniqueness half of the universal property. -/
theorem hom_ext [Mul β] {f g : SyntacticObject L →ₙ* β}
    (hlex : ∀ tok, f (SyntacticObject.leaf tok) = g (SyntacticObject.leaf tok))
    (htrace : f trace = g trace) (htraceOf : ∀ tok, f (traceOf tok) = g (traceOf tok)) :
    f = g :=
  MulHom.ext fun s => by
    induction s using SyntacticObject.ind with
    | leaf tok => exact hlex tok
    | trace => exact htrace
    | traceOf tok => exact htraceOf tok
    | merge l r ihl ihr =>
      rw [show merge l r = l * r from rfl, map_mul, map_mul, ihl, ihr]

end Minimalist.SyntacticObject
