/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.ProjectivitySignature
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Composing layers of signatures

A layer is a map from a bounded lattice to itself together with a signature that holds of it. The
layers form a submonoid of `Function.End α × ProjectivitySignature`, since function classes
compose as their signatures do and the identity is a morphism. The product of a list of layers is
therefore a layer, and its sign is the product of the signs: layers whose signs multiply to `1`
compose to a monotone map, and layers whose signs multiply to `-1` to an antitone map.

## Main definitions

* `ProjectivitySignature.classPairs`: the submonoid of layers.
* `negation`: complementation as a layer of signature `⊖`.

## Main results

* `holdsFor_list_prod`, `sign_list_prod`: the product of a list of layers is a layer, and its sign
  is the product of the signs.
* `monotone_list_prod`, `antitone_list_prod`: the composite is monotone when the signs multiply to
  `1` and antitone when they multiply to `-1`.

## References

* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

variable (α : Type*) [Lattice α] [BoundedOrder α]

/-- The maps from a bounded lattice to itself paired with a signature that holds of them, as a
submonoid of `Function.End α × ProjectivitySignature`. -/
def ProjectivitySignature.classPairs : Submonoid (Function.End α × ProjectivitySignature) where
  carrier := {p | p.2.HoldsFor p.1}
  mul_mem' {a b} ha hb := show (a.2 * b.2).HoldsFor (a.1 ∘ b.1) from
    ProjectivitySignature.HoldsFor.comp ha hb
  one_mem' := ProjectivitySignature.holdsFor_addMult_id

variable {α}

theorem ProjectivitySignature.mem_classPairs {p : Function.End α × ProjectivitySignature} :
    p ∈ ProjectivitySignature.classPairs α ↔ p.2.HoldsFor p.1 :=
  Iff.rfl

/-- Negation as a layer: complementation, anti-morphic. -/
def negation {P : Type*} [BooleanAlgebra P] : ProjectivitySignature.classPairs P :=
  ⟨(compl, .antiAddMult), ProjectivitySignature.holdsFor_antiAddMult_compl⟩

theorem ProjectivitySignature.holdsFor_list_prod {l : List (Function.End α × ProjectivitySignature)}
    (h : ∀ p ∈ l, p.2.HoldsFor p.1) : l.prod.2.HoldsFor l.prod.1 :=
  list_prod_mem (S := ProjectivitySignature.classPairs α) h

omit [Lattice α] [BoundedOrder α] in
theorem ProjectivitySignature.sign_list_prod (l : List (Function.End α × ProjectivitySignature)) :
    l.prod.2.sign = (l.map fun p ↦ p.2.sign).prod :=
  map_list_prod (ProjectivitySignature.signHom.toMonoidHom.comp (MonoidHom.snd _ _)) l

theorem ProjectivitySignature.monotone_list_prod {l : List (Function.End α × ProjectivitySignature)}
    (h : ∀ p ∈ l, p.2.HoldsFor p.1) (hs : (l.map fun p ↦ p.2.sign).prod = 1) :
    Monotone l.prod.1 :=
  (ProjectivitySignature.holdsFor_list_prod h).monotone_of_sign_eq_one
    (ProjectivitySignature.sign_list_prod l ▸ hs)

/-- A path of layers whose signs multiply to the negative sign composes to an antitone map. -/
theorem ProjectivitySignature.antitone_list_prod {l : List (Function.End α × ProjectivitySignature)}
    (h : ∀ p ∈ l, p.2.HoldsFor p.1) (hs : (l.map fun p ↦ p.2.sign).prod = -1) :
    Antitone l.prod.1 :=
  (ProjectivitySignature.holdsFor_list_prod h).antitone_of_sign_eq_neg_one
    (ProjectivitySignature.sign_list_prod l ▸ hs)

end NaturalLogic
