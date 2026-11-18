/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.UnorderedTree.Basic
public import Linglib.Core.Data.RoseTree.Licensed

/-!
# Licensed unordered trees

A relation `R` between a value and a multiset of values licenses an unordered tree when every
subtree satisfies it at its root, the daughters' labels read without order. Since `R` reads a
multiset, it [licenses every ordered representative of the tree
alike](##RoseTree.Perm.licensed_iff), so [licensing](##UnorderedTree.Licensed) descends to the
quotient. A tree is [full binary](##UnorderedTree.IsFullBinary) when the relation "no daughter or
two" licenses it.
-/

@[expose] public section

namespace UnorderedTree

variable {α : Type*}

/-- A relation `R` licenses an unordered tree when it licenses its ordered representatives, the
children's values read as a multiset. -/
def Licensed (R : α → Multiset α → Prop) (u : UnorderedTree α) : Prop :=
  Quotient.liftOn u (fun t ↦ t.Licensed fun a ks ↦ R a (ks : Multiset α)) fun _ _ h ↦
    propext (h.licensed_iff fun _ _ _ hkl ↦ by rw [Multiset.coe_eq_coe.mpr hkl])

@[simp] theorem licensed_mk (R : α → Multiset α → Prop) (t : RoseTree α) :
    (mk t).Licensed R ↔ t.Licensed fun a ks ↦ R a (ks : Multiset α) :=
  Iff.rfl

theorem Licensed.mono {R R' : α → Multiset α → Prop} (h : ∀ a ks, R a ks → R' a ks)
    {u : UnorderedTree α} (hu : u.Licensed R) : u.Licensed R' := by
  induction u using Quotient.inductionOn
  exact RoseTree.Licensed.mono (fun a ks ↦ h a ks) hu

instance (R : α → Multiset α → Prop) [∀ a ks, Decidable (R a ks)] (u : UnorderedTree α) :
    Decidable (u.Licensed R) :=
  Quotient.recOnSubsingleton u fun t ↦
    inferInstanceAs (Decidable (t.Licensed fun a ks ↦ R a (ks : Multiset α)))

/-- A tree is full binary when each of its vertices has zero or two children. -/
def IsFullBinary (u : UnorderedTree α) : Prop :=
  u.Licensed fun _ ks ↦ Multiset.card ks = 0 ∨ Multiset.card ks = 2

instance (u : UnorderedTree α) : Decidable u.IsFullBinary :=
  inferInstanceAs (Decidable (u.Licensed _))

end UnorderedTree
