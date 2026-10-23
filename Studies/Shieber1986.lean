module

public import Linglib.Morphology.Word.Features

/-!
# Shieber (1986): An Introduction to Unification-Based Approaches to Grammar

This file formalizes the information ordering of §3.2 on the token feature bundle
`Morphology.Features`, the depth-one, reentrancy-free fragment of the book's feature
structures. Every feature there is atomic-valued, so paths are single features and the
reentrancy clause of subsumption is vacuous: the definition of §3.2.2, that `D` subsumes `D′`
when `D(l)` subsumes `D′(l)` for every feature `l` of `D`, an atom neither subsuming nor
subsumed by a different one and the variable subsuming everything, is the product of the
flat orders, the bundle's `≤`, with the variable `[ ]` as `⊥`. Unification (§3.2.3) is the
most general structure both inputs subsume, failing on conflict: it succeeds exactly on
pairs bounded above and its value is their least upper bound, from which the book's example
laws follow, that unification adds information, is idempotent, has the variable as its
identity, is commutative, associative with failure propagating, and monotone. Generalization,
the most specific structure subsumed by both inputs, is total, the meet.

## Implementation notes

* The order, the partial join and the meet are the pointwise instances of
  `Core/Order/Flat.lean` and `Core/Order/PartialUnify.lean`, so each
  law is the generic lemma at `Features`. The subsumption lattice is not distributive: a
  feature with three values is the diamond, modular but not distributive, as [carpenter-1992]
  notes of feature-structure orders in general. Phrasal combination and reentrant structures
  are not formalized.

## References

* [shieber-1986]
* [carpenter-1992]
-/

@[expose] public section

namespace Shieber1986

open Morphology PartialUnify
open scoped PartialUnify

variable {f g h u : Features}

theorem le_iff : f ≤ g ↔ ∀ t, f t ≤ g t := Pi.le_def

theorem bot_le (f : Features) : ⊥ ≤ f := _root_.bot_le

theorem unify_ne_top_iff : unify f g ≠ ⊤ ↔ Compat f g := unify_ne_top_iff_bddAbove

theorem unify_eq_coe_iff_isLUB : unify f g = ↑u ↔ IsLUB {f, g} u :=
  PartialUnify.unify_eq_coe_iff_isLUB

theorem le_of_unify_eq_coe (hu : unify f g = ↑u) : f ≤ u ∧ g ≤ u :=
  unify_le_coe_iff.1 hu.le

theorem unify_self (f : Features) : unify f f = ↑f := PartialUnify.unify_self f

theorem bot_unify (f : Features) : unify ⊥ f = ↑f := PartialUnify.bot_unify f

theorem unify_bot (f : Features) : unify f ⊥ = ↑f := PartialUnify.unify_bot f

theorem unify_comm (f g : Features) : unify f g = unify g f := PartialUnify.unify_comm f g

theorem unify_assoc (f g h : Features) : unify f g ⊔ ↑h = ↑f ⊔ unify g h :=
  PartialUnify.unify_assoc f g h

theorem unify_mono {f' g' : Features} (hf : f ≤ f') (hg : g ≤ g') (hu : unify f' g' = ↑u) :
    ∃ v : Features, unify f g = ↑v ∧ v ≤ u :=
  PartialUnify.unify_mono hf hg hu

theorem le_inf_iff : h ≤ f ⊓ g ↔ h ≤ f ∧ h ≤ g := _root_.le_inf_iff

theorem unify_examples :
    unify (Features.of (person := some .third)) (Features.of (number := some .singular)) =
        ↑(Features.of (person := some .third) (number := some .singular)) ∧
      unify (Features.of (tense := some .Past)) (Features.of (tense := some .Pres)) = ⊤ := by
  decide

end Shieber1986
