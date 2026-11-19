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
  `Core/Order/Flat.lean` and `Core/Order/Compat.lean`, so each
  law is the generic lemma at `Features`. The subsumption lattice is not distributive: a
  feature with three values is the diamond, modular but not distributive, as [carpenter-1992]
  notes of feature-structure orders in general. Phrasal combination and reentrant structures
  are not formalized.

## References

* [shieber-1986]
* [carpenter-1992]
-/

public section

namespace Shieber1986

open Morphology

variable {f g h u : Features}

theorem le_iff : f ≤ g ↔ ∀ t, f t ≤ g t := Pi.le_def

theorem bot_le (f : Features) : ⊥ ≤ f := _root_.bot_le

/-- Feature structures are compatible when they are at every feature. -/
theorem compat_iff : Compat f g ↔ ∀ t, Compat (f t) (g t) := compat_pi_iff

/-- Compatible feature structures have a unification. -/
theorem exists_isLUB (hc : Compat f g) : ∃ u, IsLUB {f, g} u :=
  ⟨fun t ↦ (f t).or (g t), isLUB_pair_pi_iff.2 fun t ↦ (hc.apply t).isLUB_or⟩

theorem compat_of_isLUB (hu : IsLUB {f, g} u) : Compat f g := ⟨u, hu.1⟩

theorem le_of_isLUB (hu : IsLUB {f, g} u) : f ≤ u ∧ g ≤ u := mem_upperBounds_pair.1 hu.1

theorem isLUB_self (f : Features) : IsLUB {f, f} f := by
  rw [Set.pair_eq_singleton]
  exact isLUB_singleton

theorem isLUB_bot_left (f : Features) : IsLUB {⊥, f} f :=
  isLUB_pair_iff_forall_le.2 ⟨_root_.bot_le, le_rfl, fun _ _ hf ↦ hf⟩

theorem isLUB_bot_right (f : Features) : IsLUB {f, ⊥} f :=
  isLUB_pair_iff_forall_le.2 ⟨le_rfl, _root_.bot_le, fun _ hf _ ↦ hf⟩

theorem isLUB_comm : IsLUB {f, g} u ↔ IsLUB {g, f} u := by rw [Set.pair_comm]

/-- Unification is associative, with failure propagating. -/
theorem isLUB_assoc {v w : Features} (hv : IsLUB {f, g} v) (hw : IsLUB {v, h} w) :
    ∃ u, IsLUB {g, h} u ∧ IsLUB {f, u} w :=
  hv.pair_assoc (fun _ _ ↦ exists_isLUB) hw

/-- Unification is monotone where defined: weakening both inputs preserves success and weakens
the result. -/
theorem isLUB_mono {f' g' : Features} (hf : f ≤ f') (hg : g ≤ g') (hu : IsLUB {f', g'} u) :
    ∃ v, IsLUB {f, g} v ∧ v ≤ u :=
  have hfu := hf.trans (le_of_isLUB hu).1
  have hgu := hg.trans (le_of_isLUB hu).2
  let ⟨v, hv⟩ := exists_isLUB (.of_le hfu hgu)
  ⟨v, hv, (isLUB_le_iff hv).2 (mem_upperBounds_pair.2 ⟨hfu, hgu⟩)⟩

theorem le_inf_iff : h ≤ f ⊓ g ↔ h ≤ f ∧ h ≤ g := _root_.le_inf_iff

theorem unify_examples :
    IsLUB {Features.of (person := some .third), Features.of (number := some .singular)}
        (Features.of (person := some .third) (number := some .singular)) ∧
      ¬ Compat (Features.of (tense := some .Past)) (Features.of (tense := some .Pres)) := by
  decide

end Shieber1986
