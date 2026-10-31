/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Soundness
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Composing layers of sound signatures

The maps for which a signature is sound, each paired with that signature, form a submonoid of
`Function.End α × Signature` (`Signature.soundPairs`), since soundness composes along
`Signature.compose` and the identity is a morphism. A path of such layers is therefore sound for the
product of its signatures, the projectivity of a position, and the sign of that product is the
product of the signs of the layers. The sign fixes the direction of the composite: it is monotone
under a positive sign and antitone under a negative one, so composing with a layer of negative sign
reverses the direction ([`antitone_list_prod`](##NaturalLogic.Signature.antitone_list_prod)).

## References

* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

variable (α : Type*) [Lattice α] [BoundedOrder α]

/-- The maps paired with a signature sound for them, a submonoid of `Function.End α × Signature`:
soundness composes along `Signature.compose`, and the identity is a morphism. -/
def Signature.soundPairs : Submonoid (Function.End α × Signature) where
  carrier := {p | p.2.SoundFor p.1}
  mul_mem' {a b} ha hb :=
    show (a.2 * b.2).SoundFor (a.1 ∘ b.1) from Signature.SoundFor.comp ha hb
  one_mem' := soundFor_addMult_id

variable {α}

theorem Signature.mem_soundPairs {p : Function.End α × Signature} :
    p ∈ Signature.soundPairs α ↔ p.2.SoundFor p.1 :=
  Iff.rfl

theorem Signature.soundFor_list_prod {l : List (Function.End α × Signature)}
    (h : ∀ p ∈ l, p.2.SoundFor p.1) : l.prod.2.SoundFor l.prod.1 :=
  list_prod_mem (S := Signature.soundPairs α) h

omit [Lattice α] [BoundedOrder α] in
theorem Signature.sign_list_prod (l : List (Function.End α × Signature)) :
    l.prod.2.sign = (l.map fun p ↦ p.2.sign).prod :=
  map_list_prod (Signature.signHom.comp (MonoidHom.snd _ _)) l

theorem Signature.monotone_list_prod {l : List (Function.End α × Signature)}
    (h : ∀ p ∈ l, p.2.SoundFor p.1) (hs : (l.map fun p ↦ p.2.sign).prod = 1) :
    Monotone l.prod.1 :=
  (Signature.soundFor_list_prod h).monotone_of_sign_eq_one (Signature.sign_list_prod l ▸ hs)

/-- A path of layers whose signs multiply to the negative sign composes to an antitone map. -/
theorem Signature.antitone_list_prod {l : List (Function.End α × Signature)}
    (h : ∀ p ∈ l, p.2.SoundFor p.1) (hs : (l.map fun p ↦ p.2.sign).prod = -1) :
    Antitone l.prod.1 :=
  (Signature.soundFor_list_prod h).antitone_of_sign_eq_neg_one (Signature.sign_list_prod l ▸ hs)

end NaturalLogic
