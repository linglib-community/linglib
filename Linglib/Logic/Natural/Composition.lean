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

The maps in the function class of a signature, each paired with that signature, form a submonoid of
`Function.End α × ProjectivitySignature` (`ProjectivitySignature.classPairs`), since function
classes compose along `ProjectivitySignature.compose` and the identity is a morphism. A path of such
layers is therefore in the class of the product of its signatures, the projectivity of a position,
and the sign of that product is the product of the signs of the layers. The sign fixes the direction
of the composite: it is monotone under a positive sign and antitone under a negative one, so
composing with a layer of negative sign reverses the direction
([`antitone_list_prod`](##NaturalLogic.ProjectivitySignature.antitone_list_prod)).

## References

* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

variable (α : Type*) [Lattice α] [BoundedOrder α]

/-- The maps paired with a signature whose function class contains them, a submonoid of
`Function.End α × ProjectivitySignature`: function classes compose along
`ProjectivitySignature.compose`, and the identity is a morphism. -/
def ProjectivitySignature.classPairs : Submonoid (Function.End α × ProjectivitySignature) where
  carrier := {p | p.2.HoldsFor p.1}
  mul_mem' {a b} ha hb := show (a.2 * b.2).HoldsFor (a.1 ∘ b.1) from
    ProjectivitySignature.HoldsFor.comp ha hb
  one_mem' := ProjectivitySignature.holdsFor_addMult_id

variable {α}

theorem ProjectivitySignature.mem_classPairs {p : Function.End α × ProjectivitySignature} :
    p ∈ ProjectivitySignature.classPairs α ↔ p.2.HoldsFor p.1 :=
  Iff.rfl

theorem ProjectivitySignature.holdsFor_list_prod {l : List (Function.End α × ProjectivitySignature)}
    (h : ∀ p ∈ l, p.2.HoldsFor p.1) : l.prod.2.HoldsFor l.prod.1 :=
  list_prod_mem (S := ProjectivitySignature.classPairs α) h

omit [Lattice α] [BoundedOrder α] in
theorem ProjectivitySignature.sign_list_prod (l : List (Function.End α × ProjectivitySignature)) :
    l.prod.2.sign = (l.map fun p ↦ p.2.sign).prod :=
  map_list_prod (ProjectivitySignature.signHom.comp (MonoidHom.snd _ _)) l

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
