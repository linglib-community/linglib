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
* `Minimalist.LinearizationState.sel`: the projection morphism to `SelectionState`.
* `Minimalist.SyntacticObject.headHom`: the head function as a morphism of magmas
  `SyntacticObject →ₙ* LinearizationState side`, refining `selCheckHom`.
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
structure LinearizationState (side : Edge) : Type where
  toOption : Option ((LexicalItem.Token × List Cat) × LinearizedSyntacticObject)
deriving DecidableEq

namespace LinearizationState

variable {side : Edge}

/-- A defined state: projecting head `tok`, residual stack `stack`, linearized object `p`. -/
def of (tok : LexicalItem.Token) (stack : List Cat) (p : LinearizedSyntacticObject) :
    LinearizationState side :=
  ⟨some ((tok, stack), p)⟩

/-- Merge-local externalization: the `selCombine` decision attaches the projecting daughter on
    the head side; `0` is absorbing. -/
instance : MulZeroClass (LinearizationState side) where
  mul x y :=
    match x, y with
    | ⟨some (s₁, p₁)⟩, ⟨some (s₂, p₂)⟩ =>
        ⟨(selCombine ⟨some s₁⟩ ⟨some s₂⟩).map fun d =>
          (d.2, (bif d.1 then p₂ else p₁).attach side (bif d.1 then p₁ else p₂))⟩
    | _, _ => ⟨none⟩
  zero := ⟨none⟩
  zero_mul _ := rfl
  mul_zero x := by rcases x with ⟨_ | _⟩ <;> rfl

theorem some_mul_some (s₁ s₂ : LexicalItem.Token × List Cat) (p₁ p₂ : LinearizedSyntacticObject) :
    (⟨some (s₁, p₁)⟩ * ⟨some (s₂, p₂)⟩ : LinearizationState side) =
      ⟨(selCombine ⟨some s₁⟩ ⟨some s₂⟩).map fun d =>
          (d.2, (bif d.1 then p₂ else p₁).attach side (bif d.1 then p₁ else p₂))⟩ := rfl

instance : CommMagma (LinearizationState side) where
  mul_comm x y := by
    match x, y with
    | ⟨none⟩, ⟨none⟩ | ⟨none⟩, ⟨some _⟩ | ⟨some _⟩, ⟨none⟩ => rfl
    | ⟨some (s₁, p₁)⟩, ⟨some (s₂, p₂)⟩ =>
      rw [some_mul_some, some_mul_some, selCombine_comm]
      rcases selCombine ⟨some s₂⟩ ⟨some s₁⟩ with _ | ⟨_ | _, _, _⟩ <;> rfl

/-- The projection to the selection state: forgetting the order description. -/
def sel : LinearizationState side →ₙ* SelectionState where
  toFun x := ⟨x.toOption.map (·.1)⟩
  map_mul' x y := by
    match x, y with
    | ⟨none⟩, _ => rfl
    | ⟨some _⟩, ⟨none⟩ => exact (mul_zero _).symm
    | ⟨some (s₁, p₁)⟩, ⟨some (s₂, p₂)⟩ =>
      rw [some_mul_some]
      simp only [Option.map_map]
      rfl

@[simp] theorem sel_of (tok : LexicalItem.Token) (stack : List Cat)
    (p : LinearizedSyntacticObject) :
    sel (of tok stack p : LinearizationState side) = .of tok stack := rfl

@[simp] theorem sel_zero : sel (0 : LinearizationState side) = 0 := rfl

/-- The linearized component, the order the head function determines; `none` off `Dom(h)`. -/
def linearized? (x : LinearizationState side) : Option LinearizedSyntacticObject :=
  x.toOption.map (·.2)

@[simp] theorem linearized?_of (tok : LexicalItem.Token) (stack : List Cat)
    (p : LinearizedSyntacticObject) :
    (of tok stack p : LinearizationState side).linearized? = some p :=
  rfl

@[simp] theorem linearized?_zero : (0 : LinearizationState side).linearized? = none := rfl

theorem linearized?_mul_eq_some {x y : LinearizationState side} {p : LinearizedSyntacticObject}
    (h : (x * y).linearized? = some p) :
    ∃ px py, x.linearized? = some px ∧ y.linearized? = some py ∧
      (p = py.attach side px ∨ p = px.attach side py) := by
  match x, y with
  | ⟨some (s₁, p₁)⟩, ⟨some (s₂, p₂)⟩ =>
    rw [some_mul_some] at h
    simp only [linearized?, Option.map_map] at h
    obtain ⟨⟨b, _⟩, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨p₁, p₂, rfl, rfl, by cases b <;> simp⟩
  | ⟨none⟩, _ => cases h
  | ⟨some _⟩, ⟨none⟩ => cases h

end LinearizationState

/-! ### Harmonic linearization -/

namespace SyntacticObject

variable (side : Edge)

/-- The linearization state of a trace: silent, and saturated as `traceState` has it, a copy of
    the phrase its token heads. -/
def traceLinearizationState : Option LexicalItem.Token → LinearizationState side
  | some tok => .of tok [] (.traceOf tok)
  | none => .of .bareTrace [] .trace

/-- The head function's value on a syntactic object: the `liftFun` of the lexical leaves and the
    silent, saturated traces. -/
def linearizationState (s : SyntacticObject) : LinearizationState side :=
  liftFun (fun tok => .of tok tok.item.sel (.leaf tok)) (traceLinearizationState side) s

@[simp] theorem linearizationState_leaf (tok : LexicalItem.Token) :
    (SyntacticObject.leaf tok).linearizationState side = .of tok tok.item.sel (.leaf tok) := rfl

@[simp] theorem linearizationState_trace :
    trace.linearizationState side = .of .bareTrace [] .trace := rfl

@[simp] theorem linearizationState_traceOf (tok : LexicalItem.Token) :
    (traceOf tok).linearizationState side = .of tok [] (.traceOf tok) := rfl

@[simp] theorem linearizationState_node (l r : SyntacticObject) :
    (merge l r).linearizationState side =
      l.linearizationState side * r.linearizationState side :=
  liftFun_merge _ _ l r

/-- The head function as a morphism of magmas ([marcolli-chomsky-berwick-2025]
    §1.13's algebraic frame): Merge multiplies constituents, `h` multiplies states. -/
noncomputable def headHom : SyntacticObject →ₙ* LinearizationState side :=
  lift (fun tok => .of tok tok.item.sel (.leaf tok)) (traceLinearizationState side)

@[simp] theorem headHom_apply (s : SyntacticObject) :
    headHom side s = s.linearizationState side := rfl

/-- Fusion: the selection component of the head function's value is the selection
    check — two morphisms agreeing on the leaves (`hom_ext`). -/
theorem sel_comp_headHom :
    LinearizationState.sel.comp (headHom side) = selCheckHom :=
  hom_ext (fun _ => rfl) rfl (fun _ => rfl)

@[simp] theorem sel_linearizationState (s : SyntacticObject) :
    LinearizationState.sel (s.linearizationState side) = s.selCheck :=
  DFunLike.congr_fun (sel_comp_headHom side) s

/-- The harmonic linearization, the projecting daughter on the head side at every node
    ([marcolli-chomsky-berwick-2025] Lemma 1.13.5); `none` off `Dom(h)`. -/
def linearize? (s : SyntacticObject) : Option LinearizedSyntacticObject :=
  (s.linearizationState side).linearized?

variable {side}

/-- The harmonic linearization is a section of forgetting the order on its domain. -/
theorem toSyntacticObject_of_linearize? {s : SyntacticObject} {p : LinearizedSyntacticObject}
    (h : s.linearize? side = some p) : p.toSyntacticObject = s := by
  induction s using ind generalizing p with
  | leaf tok | trace | traceOf tok => obtain rfl := Option.some.inj h; rfl
  | merge l r ihl ihr =>
    rw [linearize?, linearizationState_node] at h
    obtain ⟨pl, pr, hl, hr, rfl | rfl⟩ := LinearizationState.linearized?_mul_eq_some h
    · rw [LinearizedSyntacticObject.toSyntacticObject_attach, ihl hl, ihr hr]
    · rw [LinearizedSyntacticObject.toSyntacticObject_attach, ihl hl, ihr hr, merge_comm]

theorem linearizationState_eq_of_linearize? {s : SyntacticObject} {p : LinearizedSyntacticObject}
    (h : s.linearize? side = some p) :
    ∃ σ, s.selCheck = ⟨some σ⟩ ∧ s.linearizationState side = ⟨some (σ, p)⟩ := by
  rcases hx : s.linearizationState side with ⟨_ | ⟨σ, q⟩⟩
  · simp [linearize?, hx, LinearizationState.linearized?] at h
  · simp only [linearize?, hx, LinearizationState.linearized?, Option.map_some,
      Option.some.injEq] at h
    subst h
    exact ⟨σ, by rw [← sel_linearizationState side s, hx]; rfl, rfl⟩

/-- Merging `d` on edge `e` of `l` is harmonic when `d` projects exactly if `e` is the head
side. -/
theorem linearize?_merge {d l : SyntacticObject} {pd pl : LinearizedSyntacticObject} {e : Edge}
    (hd : d.linearize? side = some pd) (hl : l.linearize? side = some pl)
    (h : selSide d.selCheck l.selCheck = some (decide (e = side))) :
    (merge d l).linearize? side = some (pl.attach e pd) := by
  obtain ⟨σd, hσd, hsd⟩ := linearizationState_eq_of_linearize? hd
  obtain ⟨σl, hσl, hsl⟩ := linearizationState_eq_of_linearize? hl
  rw [hσd, hσl, selSide] at h
  obtain ⟨⟨_, x⟩, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [linearize?, linearizationState_node, hsd, hsl, LinearizationState.some_mul_some, hc]
  cases e <;> cases side <;> rfl

theorem linearize?_of_mem_subtrees {cur : SyntacticObject} {pc : LinearizedSyntacticObject}
    (hc : cur.linearize? side = some pc) {q : RoseTree Vertex} (hq : q ∈ pc.val.subtrees)
    (hqs : IsSyntacticObject (mk q)) :
    linearize? side ⟨mk q, hqs⟩ = some (⟨q, hqs⟩ : LinearizedSyntacticObject) := by
  have root : ∀ {cur : SyntacticObject} {pc : LinearizedSyntacticObject},
      cur.linearize? side = some pc → ∀ hqs : IsSyntacticObject (mk pc.val),
      linearize? side ⟨mk pc.val, hqs⟩ = some (⟨pc.val, hqs⟩ : LinearizedSyntacticObject) :=
    fun hc _ ↦ by
      rw [show (⟨_, _⟩ : SyntacticObject) = _ from toSyntacticObject_of_linearize? hc, hc]; rfl
  induction cur using ind generalizing pc with
  | leaf tok | trace | traceOf tok =>
    obtain rfl := Option.some.inj hc
    simp only [LinearizedSyntacticObject.leaf_val, LinearizedSyntacticObject.trace_val,
      LinearizedSyntacticObject.traceOf_val, RoseTree.subtrees_node, List.flatMap_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact root hc hqs
  | merge l r ihl ihr =>
    have hc' := hc
    rw [linearize?, linearizationState_node] at hc'
    obtain ⟨pl, pr, hl, hr, rfl | rfl⟩ := LinearizationState.linearized?_mul_eq_some hc' <;>
      cases side <;>
      simp only [LinearizedSyntacticObject.attach, LinearizedSyntacticObject.merge_val,
        RoseTree.subtrees_node,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        List.mem_append] at hq <;>
      rcases hq with rfl | hq | hq
    all_goals first
      | exact root hc hqs
      | exact ihl hl hq
      | exact ihr hr hq

end SyntacticObject

end Minimalist
