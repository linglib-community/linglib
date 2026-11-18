/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Prosody.Structure
public import Mathlib.ModelTheory.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Prosodic structures as first-order structures

A prosodic structure is a relational model in the sense in which [jardine-danis-iacoponi-2021]
compare theories of representation: a domain of nodes with binary relations of dominance and
precedence and a unary relation for each label. This file gives the signature and reads a
prosodic structure as a first-order structure over it, as mathlib reads a simple graph as a
structure in the language of graphs. An isomorphism of prosodic structures
[is an equivalence of first-order structures](##Prosody.Structure.isoEquiv), so ordered trees
[are equal when their models are equivalent](##Prosody.Structure.nonempty_equiv_ofTree_iff).

## References

* [jardine-danis-iacoponi-2021]
-/

@[expose] public section

open FirstOrder FirstOrder.Language

namespace Prosody

namespace Structure

universe u v

/-- The relation symbols of prosodic structures: dominance, precedence, and a label for each
element of `α`. -/
inductive Rel (α : Type v) : ℕ → Type v
  | dominates : Rel α 2
  | precedes : Rel α 2
  | label (a : α) : Rel α 1

/-- The signature of prosodic structures with labels in `α`. -/
def language (α : Type v) : Language := ⟨fun _ ↦ Empty, Rel α⟩

variable {α : Type v} {X Y : Structure.{u} α}

/-- A prosodic structure is a first-order structure in the signature of dominance, precedence
and labels. -/
instance firstOrder (X : Structure.{u} α) : (language α).Structure X.Node where
  funMap := fun {_} (f : Empty) _ ↦ nomatch f
  RelMap
    | .dominates, x => x 0 ≤ x 1
    | .precedes, x => X.Precedes (x 0) (x 1)
    | .label a, x => X.label (x 0) = a

@[simp] theorem relMap_dominates (x : Fin 2 → X.Node) :
    Structure.RelMap (L := language α) Rel.dominates x ↔ x 0 ≤ x 1 := Iff.rfl

@[simp] theorem relMap_precedes (x : Fin 2 → X.Node) :
    Structure.RelMap (L := language α) Rel.precedes x ↔ X.Precedes (x 0) (x 1) := Iff.rfl

@[simp] theorem relMap_label (a : α) (x : Fin 1 → X.Node) :
    Structure.RelMap (L := language α) (Rel.label a) x ↔ X.label (x 0) = a := Iff.rfl

/-- An isomorphism of prosodic structures is an equivalence of first-order structures. -/
def Iso.toEquiv (e : Iso X Y) : X.Node ≃[language α] Y.Node where
  toEquiv := e.toOrderIso.toEquiv
  map_fun' := fun {_} (f : Empty) _ ↦ nomatch f
  map_rel' := fun {_} r x ↦ by
    cases r with
    | dominates => exact e.toOrderIso.le_iff_le
    | precedes => exact e.precedes_iff _ _
    | label a =>
      change Y.label (e.toOrderIso (x 0)) = a ↔ X.label (x 0) = a
      rw [e.label_comp]

/-- An equivalence of first-order structures is an isomorphism of prosodic structures. -/
def Iso.ofEquiv (f : X.Node ≃[language α] Y.Node) : Iso X Y where
  toOrderIso := ⟨f.toEquiv, fun {a b} ↦ f.map_rel' Rel.dominates ![a, b]⟩
  precedes_iff a b := f.map_rel' Rel.precedes ![a, b]
  label_comp a := (f.map_rel' (Rel.label (X.label a)) ![a]).2 rfl

/-- The isomorphisms of prosodic structures are the equivalences of their first-order
structures. -/
def isoEquiv : Iso X Y ≃ (X.Node ≃[language α] Y.Node) where
  toFun := Iso.toEquiv
  invFun := Iso.ofEquiv
  left_inv _ := rfl
  right_inv _ := Language.Equiv.ext fun _ ↦ rfl

/-- Ordered trees whose models are equivalent are equal. -/
theorem nonempty_equiv_ofTree_iff {t t' : RoseTree α} :
    Nonempty ((ofTree t).Node ≃[language α] (ofTree t').Node) ↔ t = t' :=
  (Equiv.nonempty_congr isoEquiv).symm.trans nonempty_iso_ofTree_iff

end Structure

end Prosody
