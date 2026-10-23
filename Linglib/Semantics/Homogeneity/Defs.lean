module

public import Linglib.Logic.Trivalent.Pointwise
public import Mathlib.Order.SetNotation

/-!
# Homogeneity

A homogeneous predication, in Križ's sense, is trivalent: true when the predicate holds throughout
its specification points, false when it fails throughout, and undefined in between, at the worlds of
its extension gap `Trivalent.gapExt`. Instantiations differ in the specification points: the parts
of a plurality (`Homogeneity.readings`), closest antecedent worlds
(`Conditional.selectionalCounterfactual`), overlapping pluralities
(`Kriz2016.generalisedTruthValue`), best modal worlds (`Studies/AghaJeretic2022`). Homogeneity
removers such as *all*, *necessarily* and *completely* denote the Beaver–Krahmer assertion operator
applied pointwise, `fun w ↦ ofProp (p w = 1)`, which collapses the gap into the negative extension
(`Trivalent.isBivalent_ofProp_eq_one`). A family of propositions is `Homogeneous` at a world when
its members are all true there or all false there, which is where the supervaluation over them is
defined; presuppositional exhaustification presupposes this of its includable alternatives.

## Main declarations

* `Homogeneous`: the members of a family of propositions agree at a world.
* `homogeneous_coe_iff`: on a finite family, agreement is definedness of the supervaluation.

## References

* [kriz-2016]
* [kriz-2015]
* [delpinal-bassi-sauerland-2024]
-/

@[expose] public section

namespace Homogeneity

variable {W : Type*}

/-- The propositions of `S` are homogeneous at `w` when they are all true there or all false
there. -/
def Homogeneous (S : Set (Set W)) (w : W) : Prop :=
  (∀ α ∈ S, w ∈ α) ∨ ∀ α ∈ S, w ∉ α

section Homogeneous

variable {S : Set (Set W)} {φ : Set W} {w : W}

@[simp] theorem homogeneous_empty : Homogeneous (∅ : Set (Set W)) w :=
  .inl fun _ h ↦ h.elim

@[simp] theorem homogeneous_pair {p q : Set W} : Homogeneous {p, q} w ↔ (w ∈ p ↔ w ∈ q) := by
  grind [Homogeneous]

theorem homogeneous_coe_iff (s : Finset (Set W)) [DecidablePred fun α : Set W ↦ w ∈ α] :
    Homogeneous (s : Set (Set W)) w ↔ SignType.supervaluation s (w ∈ ·) ≠ 0 := by
  rw [Ne, SignType.supervaluation_eq_zero_iff]
  grind [Homogeneous]

theorem Homogeneous.mem_iff (h : Homogeneous S w) (hl : ⋂₀ S ⊆ φ) (hu : φ ⊆ ⋃₀ S) :
    w ∈ φ ↔ ∀ α ∈ S, w ∈ α := by
  grind [Homogeneous]

theorem Homogeneous.notMem_iff (h : Homogeneous S w) (hl : ⋂₀ S ⊆ φ) (hu : φ ⊆ ⋃₀ S) :
    w ∉ φ ↔ ∀ α ∈ S, w ∉ α := by
  grind [Homogeneous]

end Homogeneous

end Homogeneity
