/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.Selection

/-!
# Harmonic externalization

A head function on a binary tree determines a planar embedding of it, and conversely
([marcolli-chomsky-berwick-2025] Lemmas 1.13.4 and 1.13.5), and the book reads the head
function's value on a tree as the ordered leaves of that embedding (eq. (1.13.3)). Lemma 1.13.7
identifies head functions with bare-phrase-structure projection ([chomsky-1995-bare]); composed
with [adger-2003]'s identification of the projecting item as the selecting item (a synthesis
step of this formalization, not a claim of the book), c-selection computes the embedding. The
harmonic linearization `SyntacticObject.linearize?` places the projecting daughter on a
language's head side at every node. It is the linearized component of the head function's value,
a morphism of commutative magmas out of the carrier (`SyntacticObject.headHom`), and a section of
forgetting the order wherever every node has a head
(`SyntacticObject.toSyntacticObject_of_linearize?`): the harmonic candidate for the book's
externalization section σ_L, which must extend it noncanonically off that domain.

## Main declarations

* `Minimalist.LinearizationState`: the value of the head function in its two descriptions, the
  selection state and the linearized object the head determines, `0` off `Dom(h)`; a `CommMagma`
  and `MulZeroClass` under the Merge-local product.
* `Minimalist.LinearizationState.sel`: the projection morphism to `SelectionRule.stack.State`.
* `Minimalist.SyntacticObject.headHom`: the head function as a morphism of magmas
  `SyntacticObject →ₙ* LinearizationState side`, refining `selectionState`.
* `Minimalist.SyntacticObject.linearize?`: the harmonic linearization.

## Main results

* `Minimalist.SyntacticObject.sel_comp_headHom`: fusion, the selection component of the head
  function's value being the selection check, by `SyntacticObject.hom_ext`.
* `Minimalist.SyntacticObject.toSyntacticObject_of_linearize?`: the harmonic linearization is a
  section of forgetting the order on its domain.
* `Minimalist.SyntacticObject.linearize?_merge`: a daughter merged on an edge is linearized there
  when it projects exactly if the edge is the head side.

## Implementation notes

The head side is an `Edge`, `left` for head-initial and `right` for head-final. Head functions
are partial ([marcolli-chomsky-berwick-2025] §1.13.2): at exocentric nodes no daughter projects
and no order is determined, the book rejecting an order induced from a total order on labels as
"not a realistic linguistic assumption", so the state is `0` there, the absorbing element of the
book's renormalization reading of partial head functions. The selection state and the linearized
object are the book's two descriptions of *one* head function: eq. (1.13.3) reads `h(T)` as "a
single leaf (the head)" or as the ordered leaves of the planar embedding it determines,
"switch[ing] between these two descriptions without changing the notation". `LinearizationState`
fuses them into one partial value, so the linearization is defined exactly on `Dom(h)`.
**Naming**: the head-function *maps* (`headHom` and the leaf data it lifts) carry the book's name
for `h`; the *value* type does not, the book restricting "the term head to terminal elements"
(quoting [chomsky-1995-bare] §4), and the strict head is recovered via `sel`.

Only the two harmonic sections are realized: uniform head-side placement is right for
head–complement structure but does not model specifier placement, which needs a head side per
category.

## References

* [marcolli-chomsky-berwick-2025], §1.12.1 and §1.13
* [chomsky-1995-bare]
* [adger-2003]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree

/-! ### The linearization state -/

/-- The value of the head function in its two descriptions: the projecting head with its residual
    stack, and the linearized object it determines; `0` off `Dom(h)`. The head side is phantom in
    the carrier; the multiplication reads it. -/
structure LinearizationState (side : Edge) (ι : Type := LexicalItem.Token) : Type where
  toOption : Option
      (SelectionRule.stack.Constituent × PlanarSyntacticObject
      (SyntacticObject.Leaf LexicalItem.Token ι))
deriving DecidableEq

namespace LinearizationState

variable {side : Edge} {ι : Type}

/-- A defined state: projecting head `tok`, residual stack `stack`, linearized object `p`. -/
def of (tok : LexicalItem.Token) (stack : List Cat)
    (p : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    LinearizationState side ι :=
  ⟨some (⟨tok, stack⟩, p)⟩

/-- Merge-local externalization: the sister that projects is attached on the head side, the
    other on the other side; `0` is absorbing. -/
instance : MulZeroClass (LinearizationState side ι) where
  mul x y :=
    match x, y with
    | ⟨some (s₁, p₁)⟩, ⟨some (s₂, p₂)⟩ =>
        if s₁.Projects s₂ then ⟨some (s₁.select s₂, p₂.attach side p₁)⟩
        else if s₂.Projects s₁ then ⟨some (s₂.select s₁, p₁.attach side p₂)⟩ else ⟨none⟩
    | _, _ => ⟨none⟩
  zero := ⟨none⟩
  zero_mul _ := rfl
  mul_zero x := by rcases x with ⟨_ | _⟩ <;> rfl

theorem some_mul_some (s₁ s₂ : SelectionRule.stack.Constituent)
    (p₁ p₂ : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    (⟨some (s₁, p₁)⟩ * ⟨some (s₂, p₂)⟩ : LinearizationState side ι) =
      if s₁.Projects s₂ then ⟨some (s₁.select s₂, p₂.attach side p₁)⟩
      else if s₂.Projects s₁ then ⟨some (s₂.select s₁, p₁.attach side p₂)⟩ else ⟨none⟩ := rfl

instance : CommMagma (LinearizationState side ι) where
  mul_comm x y := by
    match x, y with
    | ⟨none⟩, ⟨none⟩ | ⟨none⟩, ⟨some _⟩ | ⟨some _⟩, ⟨none⟩ => rfl
    | ⟨some (s₁, p₁)⟩, ⟨some (s₂, p₂)⟩ =>
      rw [some_mul_some, some_mul_some]
      by_cases h : s₁.Projects s₂
      · simp [h, h.asymm]
      · by_cases h' : s₂.Projects s₁ <;> simp [h, h']

/-- The projection to the selection state: forgetting the order description. -/
def sel : LinearizationState side ι →ₙ* SelectionRule.stack.State where
  toFun x := ⟨x.toOption.map (·.1)⟩
  map_mul' x y := by
    match x, y with
    | ⟨none⟩, _ => rfl
    | ⟨some _⟩, ⟨none⟩ => exact (mul_zero _).symm
    | ⟨some (s₁, p₁)⟩, ⟨some (s₂, p₂)⟩ =>
      rw [some_mul_some]
      show _ = SelectionRule.State.merge s₁ s₂
      unfold SelectionRule.State.merge
      split_ifs <;> rfl

@[simp] theorem sel_of (tok : LexicalItem.Token) (stack : List Cat)
    (p : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    sel (of tok stack p : LinearizationState side ι) = .of tok stack := rfl

@[simp] theorem sel_zero : sel (0 : LinearizationState side ι) = 0 := rfl

/-- The linearized component, the order the head function determines; `none` off `Dom(h)`. -/
def linearized? (x : LinearizationState side ι) : Option
    (PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :=
  x.toOption.map (·.2)

@[simp] theorem linearized?_of (tok : LexicalItem.Token) (stack : List Cat)
    (p : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) :
    (of tok stack p : LinearizationState side ι).linearized? = some p :=
  rfl

@[simp] theorem linearized?_zero : (0 : LinearizationState side ι).linearized? = none := rfl

theorem linearized?_mul_eq_some {x y : LinearizationState side ι}
    {p : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    (h : (x * y).linearized? = some p) :
    ∃ px py, x.linearized? = some px ∧ y.linearized? = some py ∧
      (p = py.attach side px ∨ p = px.attach side py) := by
  match x, y with
  | ⟨some (s₁, p₁)⟩, ⟨some (s₂, p₂)⟩ =>
    rw [some_mul_some] at h
    split_ifs at h
    · exact ⟨p₁, p₂, rfl, rfl, .inl (Option.some.inj h).symm⟩
    · exact ⟨p₁, p₂, rfl, rfl, .inr (Option.some.inj h).symm⟩
    · cases h
  | ⟨none⟩, _ => cases h
  | ⟨some _⟩, ⟨none⟩ => cases h

end LinearizationState

/-! ### Linearizations

A morphism of magmas into the linearization states linearizes when the state of a leaf, where it
is defined, holds that leaf. Its value on an object is then an order of that object, the
projecting daughter on the head side at every node. -/

section Linearizes

open SyntacticObject

variable {side : Edge} {ι : Type}
  {φ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) →ₙ* LinearizationState side ι}

/-- A morphism into the linearization states linearizes when the state of a leaf, where it is
defined, holds that leaf. -/
def LinearizationState.Linearizes
    (φ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) →ₙ* LinearizationState side ι) :
    Prop :=
  ∀ ℓ p, (φ (FreeCommMagma.of ℓ)).linearized? = some p → p = FreeMagma.of ℓ

namespace LinearizationState.Linearizes

variable (hφ : Linearizes φ)
include hφ

/-- A linearization is a section of forgetting the order on its domain. -/
theorem toSyntacticObject_eq {s : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    {p : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    (h : (φ s).linearized? = some p) : p.toSyntacticObject = s := by
  induction s using ind generalizing p with
  | leaf tok | trace | traceOf tok => obtain rfl := hφ _ _ h; rfl
  | merge l r ihl ihr =>
    rw [show merge l r = l * r from rfl, map_mul] at h
    obtain ⟨pl, pr, hl, hr, rfl | rfl⟩ := linearized?_mul_eq_some h
    · rw [PlanarSyntacticObject.toSyntacticObject_attach, ihl hl, ihr hr]
    · rw [PlanarSyntacticObject.toSyntacticObject_attach, ihl hl, ihr hr, merge_comm]

omit hφ in
theorem eq_of_linearized? {s : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    {p : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    (h : (φ s).linearized? = some p) : ∃ σ, sel (φ s) = ⟨some σ⟩ ∧ φ s = ⟨some (σ, p)⟩ := by
  rcases hx : φ s with ⟨_ | ⟨σ, q⟩⟩
  · simp [hx, linearized?] at h
  · simp only [hx, linearized?, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨σ, rfl, rfl⟩

omit hφ in
/-- Merging `d` on edge `e` of `l` is harmonic when `d` projects exactly if `e` is the head
side. -/
theorem linearized?_merge {d l : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    {pd pl : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)} {e : Edge}
    (hd : (φ d).linearized? = some pd) (hl : (φ l).linearized? = some pl)
    (h : SelectionRule.State.side (sel (φ d)) (sel (φ l)) = some (decide (e = side))) :
    (φ (merge d l)).linearized? = some (pl.attach e pd) := by
  obtain ⟨σd, hσd, hsd⟩ := eq_of_linearized? hd
  obtain ⟨σl, hσl, hsl⟩ := eq_of_linearized? hl
  rw [hσd, hσl] at h
  change (if σd.Projects σl then some true else if σl.Projects σd then some false else none) =
    some (decide (e = side)) at h
  rw [show merge d l = d * l from rfl, map_mul, hsd, hsl, some_mul_some]
  split_ifs at h ⊢ with h₁ h₂ <;> cases e <;> cases side <;> first | rfl | simp at h

/-- The subtrees of a linearized object are the linearizations of its terms. -/
theorem linearized?_of_mem_subtrees
    {cur : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    {pc : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
        (hc : (φ cur).linearized? = some pc)
    {q : RoseTree (Vertex LexicalItem.Token ι)} (hq : q ∈ pc.toRoseTree.subtrees)
    (hqs : IsSyntacticObject (UnorderedTree.mk q)) :
    (φ (ofUnorderedTree (UnorderedTree.mk q) hqs)).linearized? =
      some (PlanarSyntacticObject.ofRoseTree q hqs) := by
  have root : ∀ {cur : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
      {pc : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)},
      (φ cur).linearized? = some pc → ∀ hqs : IsSyntacticObject (UnorderedTree.mk pc.toRoseTree),
      (φ (ofUnorderedTree (UnorderedTree.mk pc.toRoseTree) hqs)).linearized? =
          some (PlanarSyntacticObject.ofRoseTree pc.toRoseTree hqs) :=
    fun hc _ ↦ by
      rw [← PlanarSyntacticObject.toSyntacticObject_ofRoseTree,
        PlanarSyntacticObject.ofRoseTree_toRoseTree, hφ.toSyntacticObject_eq hc, hc]
  induction cur using ind generalizing pc with
  | leaf tok | trace | traceOf tok =>
    obtain rfl := hφ _ _ hc
    simp only [show ∀ ℓ : Leaf LexicalItem.Token ι,
        (PlanarSyntacticObject.toRoseTree (FreeMagma.of ℓ)).subtrees =
          [PlanarSyntacticObject.toRoseTree (FreeMagma.of ℓ)] from fun ℓ ↦ by cases ℓ <;> rfl,
      List.mem_singleton] at hq
    subst hq
    exact root hc hqs
  | merge l r ihl ihr =>
    have hc' := hc
    rw [show merge l r = l * r from rfl, map_mul] at hc'
    obtain ⟨pl, pr, hl, hr, rfl | rfl⟩ := linearized?_mul_eq_some hc' <;>
      cases side <;>
      simp only [PlanarSyntacticObject.attach, PlanarSyntacticObject.toRoseTree_merge,
        RoseTree.subtrees_node,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        List.mem_append] at hq <;>
      rcases hq with rfl | hq | hq
    all_goals first
      | exact root hc hqs
      | exact ihl hl hq
      | exact ihr hr hq

end LinearizationState.Linearizes

end Linearizes

/-! ### Harmonic linearization -/

namespace SyntacticObject

variable (side : Edge)

/-- The linearization state of a trace: silent, and saturated as `traceState` has it, a copy of
    the phrase its token heads. -/
def traceLinearizationState : Option LexicalItem.Token → LinearizationState side
  | some tok => .of tok [] (.traceOf tok)
  | none => .of .bareTrace [] .trace

/-- The head function as a morphism of magmas ([marcolli-chomsky-berwick-2025]
    §1.13's algebraic frame): Merge multiplies constituents, `h` multiplies states. -/
def headHom : SyntacticObject TokenLeaf →ₙ* LinearizationState side :=
  FreeCommMagma.lift
    (Leaf.elim (fun tok ↦ .of tok tok.item.sel (.leaf tok)) (traceLinearizationState side))

@[simp] theorem headHom_leaf (tok : LexicalItem.Token) :
    headHom side (SyntacticObject.leaf tok) = .of tok tok.item.sel (.leaf tok) := rfl

@[simp] theorem headHom_trace :
    headHom side (trace : SyntacticObject TokenLeaf) = .of .bareTrace [] .trace := rfl

@[simp] theorem headHom_traceOf (tok : LexicalItem.Token) :
    headHom side (traceOf tok) = .of tok [] (.traceOf tok) := rfl

/-- Fusion: the selection component of the head function's value is the selection
    check — two morphisms agreeing on the leaves (`hom_ext`). -/
theorem sel_comp_headHom :
    LinearizationState.sel.comp (headHom side) = selectionState :=
  FreeCommMagma.hom_ext fun x ↦ by cases x <;> rfl

@[simp] theorem sel_headHom (s : SyntacticObject TokenLeaf) :
    LinearizationState.sel (headHom side s) = selectionState s :=
  DFunLike.congr_fun (sel_comp_headHom side) s

/-- The harmonic linearization, the projecting daughter on the head side at every node
    ([marcolli-chomsky-berwick-2025] Lemma 1.13.5); `none` off `Dom(h)`. -/
def linearize? (s : SyntacticObject TokenLeaf) : Option (PlanarSyntacticObject TokenLeaf) :=
  (headHom side s).linearized?

variable {side}

/-- The head function linearizes. -/
theorem headHom_linearizes : LinearizationState.Linearizes (headHom side) := fun ℓ p h ↦ by
  cases ℓ <;> exact (Option.some.inj h).symm

end SyntacticObject

end Minimalist
