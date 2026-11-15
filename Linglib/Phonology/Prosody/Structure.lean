/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Positions
public import Mathlib.Order.Hom.Basic

/-!
# Prosodic structures

Accounts of prosodic structure differ in what they take a representation to be: a tree of
constituents, tiers joined by association lines, a grid. What they share is a set of nodes, each
with a label, standing in two relations: dominance, by which one node contains another, and
precedence, by which one comes before another. A prosodic structure is that shared
object, and an account is related to the others by the map that sends its representations to
prosodic structures, by which structures are in the image of that map, and by what the map
forgets.

An ordered tree denotes [the structure of its positions](##Prosody.Structure.ofTree), which
[is tree-shaped](##Prosody.Structure.isTree_ofTree): it has a root, and any two nodes are
related by dominance or by precedence, never both, with precedence inherited by what is
dominated. Trees with isomorphic structures
[are equal](##Prosody.Structure.nonempty_iso_ofTree_iff). A tree-shaped structure
[has no crossing](##Prosody.Structure.IsTree.noCrossing), the condition that if one node
precedes another then nothing the second properly dominates precedes anything the first
properly dominates. No Crossing mentions neither tiers nor lines, and unlike tree shape it
allows a node two mothers, as a geminate has.

## Implementation notes

Dominance is the order of the nodes with the dominating node least, as for the positions of a
tree, so that the root is the bottom element. Precedence is given and not derived from
dominance, and an account need not relate every two nodes by one or the other: a node stranded
by the loss of its mother keeps its place among the nodes of its kind, and has none among the
segments it is not linked to. Nor need one node be wholly before another that it precedes:
two syllables that share a geminate stand in precedence. The event structures of
[bird-klein-1990] take precedence in the strict sense, disjoint from overlap, and have
dominance as a further relation.

## References

* [sagey-1988]
* [bird-klein-1990]
-/

@[expose] public section

namespace Prosody

open RoseTree

universe u v

/-- A prosodic structure with labels in `α`: nodes ordered by dominance, the dominating node
least, with a relation of precedence and a label at each node. -/
structure Structure (α : Type v) where
  /-- The nodes. -/
  Node : Type u
  /-- Dominance, the dominating node least. -/
  [dominance : PartialOrder Node]
  /-- `Precedes a b`: the node `a` comes before `b`. -/
  Precedes : Node → Node → Prop
  /-- The label of a node. -/
  label : Node → α

attribute [instance] Structure.dominance

namespace Structure

variable {α : Type v} {X Y Z : Structure.{u} α}

/-! ### Maps -/

/-- A map of prosodic structures preserves dominance, precedence and labels. -/
structure Hom (X Y : Structure.{u} α) extends X.Node →o Y.Node where
  /-- Precedence is preserved. -/
  map_precedes ⦃a b : X.Node⦄ : X.Precedes a b → Y.Precedes (toFun a) (toFun b)
  /-- Labels are preserved. -/
  label_comp (a : X.Node) : Y.label (toFun a) = X.label a

/-- The identity map. -/
def Hom.id (X : Structure.{u} α) : Hom X X :=
  ⟨OrderHom.id, fun _ _ h ↦ h, fun _ ↦ rfl⟩

/-- The composition of maps. -/
def Hom.comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z :=
  ⟨g.toOrderHom.comp f.toOrderHom, fun _ _ h ↦ g.map_precedes (f.map_precedes h),
    fun a ↦ (g.label_comp _).trans (f.label_comp a)⟩

/-- An isomorphism of prosodic structures: a bijection of nodes preserving and reflecting
dominance and precedence, and preserving labels. -/
structure Iso (X Y : Structure.{u} α) where
  /-- The bijection of nodes, preserving and reflecting dominance. -/
  toOrderIso : X.Node ≃o Y.Node
  /-- Precedence corresponds. -/
  precedes_iff (a b : X.Node) : Y.Precedes (toOrderIso a) (toOrderIso b) ↔ X.Precedes a b
  /-- Labels are preserved. -/
  label_comp (a : X.Node) : Y.label (toOrderIso a) = X.label a

/-- The identity isomorphism. -/
def Iso.refl (X : Structure.{u} α) : Iso X X :=
  ⟨OrderIso.refl _, fun _ _ ↦ Iff.rfl, fun _ ↦ rfl⟩

/-- The inverse isomorphism. -/
def Iso.symm (e : Iso X Y) : Iso Y X where
  toOrderIso := e.toOrderIso.symm
  precedes_iff a b := by
    simpa using (e.precedes_iff (e.toOrderIso.symm a) (e.toOrderIso.symm b)).symm
  label_comp a := by simpa using (e.label_comp (e.toOrderIso.symm a)).symm

/-- The composition of isomorphisms. -/
def Iso.trans (e : Iso X Y) (f : Iso Y Z) : Iso X Z where
  toOrderIso := e.toOrderIso.trans f.toOrderIso
  precedes_iff a b := (f.precedes_iff _ _).trans (e.precedes_iff a b)
  label_comp a := (f.label_comp _).trans (e.label_comp a)

/-- An isomorphism is a map. -/
def Iso.toHom (e : Iso X Y) : Hom X Y :=
  ⟨e.toOrderIso.toOrderEmbedding.toOrderHom, fun a b h ↦ (e.precedes_iff a b).2 h, e.label_comp⟩

/-! ### Crossing and tree shape -/

variable (X) in
/-- **No Crossing**: if one node precedes another, nothing the second properly dominates
precedes anything the first properly dominates. Two lines cross; a line and a node do not. -/
def NoCrossing : Prop :=
  ∀ ⦃a a' b b' : X.Node⦄, X.Precedes a a' → a < b → a' < b' → ¬X.Precedes b' b

variable (X) in
/-- A structure is **tree-shaped** when it has a root, precedence is a strict order that relates
any two nodes unrelated by dominance, and what two nodes dominate inherits their precedence. -/
@[mk_iff]
structure IsTree : Prop where
  /-- Some node dominates every node. -/
  exists_isBot : ∃ r : X.Node, IsBot r
  /-- No node precedes itself. -/
  irrefl (a : X.Node) : ¬X.Precedes a a
  /-- Precedence is transitive. -/
  trans ⦃a b c : X.Node⦄ : X.Precedes a b → X.Precedes b c → X.Precedes a c
  /-- Two nodes are related by dominance or by precedence. -/
  le_or_precedes (a b : X.Node) : a ≤ b ∨ b ≤ a ∨ X.Precedes a b ∨ X.Precedes b a
  /-- What two nodes dominate inherits their precedence. -/
  mono ⦃a b a' b' : X.Node⦄ : X.Precedes a b → a ≤ a' → b ≤ b' → X.Precedes a' b'

namespace IsTree

variable (h : X.IsTree)
include h

/-- In a tree-shaped structure, nodes related by precedence are not related by dominance. -/
theorem not_le ⦃a b : X.Node⦄ (hab : X.Precedes a b) : ¬a ≤ b := fun hle ↦
  h.irrefl b (h.mono hab hle le_rfl)

theorem not_ge ⦃a b : X.Node⦄ (hab : X.Precedes a b) : ¬b ≤ a := fun hle ↦
  h.irrefl a (h.mono hab le_rfl hle)

/-- In a tree-shaped structure, the nodes dominating a node form a chain: a node has at most one
mother. -/
theorem isChain_Iic (a : X.Node) : IsChain (· ≤ ·) (Set.Iic a) := fun b hb c hc _ ↦ by
  rcases h.le_or_precedes b c with hbc | hcb | hp | hp
  · exact .inl hbc
  · exact .inr hcb
  · exact (h.irrefl a (h.mono hp hb hc)).elim
  · exact (h.irrefl a (h.mono hp hc hb)).elim

/-- A tree-shaped structure has no crossing. -/
theorem noCrossing : X.NoCrossing := fun _ _ _ _ hp hb hb' hp' ↦
  h.irrefl _ (h.trans (h.mono hp hb.le hb'.le) hp')

end IsTree

/-! ### The structure of a tree -/

/-- The prosodic structure of an ordered tree: its positions under dominance and left-to-right
precedence, each labelled by the node at it. -/
def ofTree (t : RoseTree α) : Structure α where
  Node := t.Positions
  Precedes p q := GornAddress.Precedes p.val q.val
  label p := p.subtree.value

@[simp] theorem ofTree_label (t : RoseTree α) (p : t.Positions) :
    (ofTree t).label p = p.subtree.value := rfl

/-- The structure of a tree is tree-shaped. -/
theorem isTree_ofTree (t : RoseTree α) : (ofTree t).IsTree where
  exists_isBot := ⟨(⊥ : t.Positions), fun p ↦ (bot_le : (⊥ : t.Positions) ≤ p)⟩
  irrefl p := GornAddress.Precedes.irrefl p.val
  trans _ _ _ := GornAddress.Precedes.trans
  le_or_precedes p q := GornAddress.Precedes.trichotomy p.val q.val
  mono _ _ _ _ hp ha hb := hp.mono ha hb

/-- Trees with isomorphic structures are equal. -/
theorem nonempty_iso_ofTree_iff {t t' : RoseTree α} :
    Nonempty (Iso (ofTree t) (ofTree t')) ↔ t = t' := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ h ▸ ⟨Iso.refl _⟩⟩
  let f : t.Positions ≃o t'.Positions := e.toOrderIso
  have key (p : t.Positions) : (f p).val = p.val :=
    Positions.val_apply_of_precedes_iff f e.precedes_iff p
  refine ext_of_getElem? fun l ↦ ?_
  by_cases hl : (⟨l⟩ : GornAddress) ∈ t.validPaths
  · have h := Positions.getElem?_eq (f ⟨⟨l⟩, hl⟩)
    rw [key] at h
    rw [Positions.getElem?_eq ⟨⟨l⟩, hl⟩, h]
    exact congrArg some (e.label_comp ⟨⟨l⟩, hl⟩).symm
  · have hl' : (⟨l⟩ : GornAddress) ∉ t'.validPaths := fun hl' ↦ hl <| by
      have h := (f.symm ⟨⟨l⟩, hl'⟩).2
      rwa [← key, f.apply_symm_apply] at h
    have h₁ : t[l]? = none := Option.not_isSome_iff_eq_none.1 hl
    have h₂ : t'[l]? = none := Option.not_isSome_iff_eq_none.1 hl'
    rw [h₁, h₂]

end Structure

end Prosody
