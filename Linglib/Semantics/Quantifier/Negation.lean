module

public import Linglib.Core.Algebra.Ring.BooleanRing
public import Linglib.Semantics.Quantifier.Restriction
public import Linglib.Semantics.Negation.Polarity
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# The negations of a quantifier

A quantifier `Q` can be negated in two places. Outer negation negates the value: it is the
complement `Qᶜ`. Inner negation negates the scope: `Q.innerNeg B = Q Bᶜ`. Doing both gives the
dual, `Q.dual B = ¬ Q Bᶜ`.

The two negations are the two ways a group acting on truth values and on sets acts on the functions
from sets to truth values. The polarities act on truth values by negation, and so on a quantifier
through its value; they act on sets by complement, and so on a quantifier through its scope, which
is the action of `DomMulAct Polarity`. The two actions commute. Together they are an action of the
pairs of an outer and an inner polarity, and the orbit of a quantifier consists of the quantifier,
its inner negation, its dual and its complement, the corners of its square of opposition in
`Quantifier/Square.lean`. A monotone or antitone quantifier stays monotone or antitone under each
action, and the direction changes once for each negative polarity.

A set `N` of individuals also acts on a quantifier, by complementing the scope within `N`. All
three actions leave the restriction of a quantifier unchanged, and the action of `N` exchanges its
positive and negative restrictions on `N`.

## Main results

* `Quantifier.negative_smul`: `Polarity.negative • Q = Qᶜ`.
* `Quantifier.mk_negative_smul`: `DomMulAct.mk Polarity.negative • Q = Q.innerNeg`.
* `Quantifier.orbit_eq`: the orbit of `Q` under the two actions is `Q`, `Q.innerNeg`, `Q.dual` and
  `Qᶜ`.
* `Quantifier.mk_toBoolRing_univ_vadd`: inner negation is the action of the whole universe on the
  scope by symmetric difference.
* `Quantifier.mk_toBoolRing_singleton_vadd_eq_iff_notMem`: on a finite universe, flipping one
  individual fixes a quantifier if and only if the individual is outside its restriction.

## Implementation notes

The action through the scope is mathlib's action of `DomMulAct M` on a function type whose domain
`M` acts on, here with the polarities acting on sets by complement. That it is an action, and that
it commutes with the action through the value, are instances of that file. A homomorphism from
pairs of polarities into the functions from quantifiers to quantifiers would say the same and
provide none of the lemmas about actions, such as that every point of an orbit has that orbit,
`MulAction.orbit_smul`.

## References

* [peters-westerstahl-2006]
-/

@[expose] public section

namespace Quantifier

variable {α : Type*} {Q : Quantifier α}

/-! ### The action of the polarities -/

open DomMulAct

@[simp] theorem negative_smul (Q : Quantifier α) : Polarity.negative • Q = Qᶜ := rfl

@[simp] theorem mk_negative_smul (Q : Quantifier α) : mk Polarity.negative • Q = Q.innerNeg := rfl

theorem negative_smul_mk_negative_smul (Q : Quantifier α) :
    Polarity.negative • mk Polarity.negative • Q = Q.dual := rfl

/-- The pairs of an outer and an inner polarity act on quantifiers, the outer one through the
value and the inner one through the scope. -/
instance : MulAction (Polarity × DomMulAct Polarity) (Quantifier α) :=
  MulAction.prodOfSMulCommClass _ _ _

/-- The orbit of a quantifier under the two actions of the polarities is the quantifier, its inner
negation, its dual and its complement. -/
theorem orbit_eq (Q : Quantifier α) :
    MulAction.orbit (Polarity × DomMulAct Polarity) Q = {Q, Q.innerNeg, Q.dual, Qᶜ} := by
  ext Q'
  simp only [MulAction.mem_orbit_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨o, i⟩, rfl⟩
    obtain ⟨i, rfl⟩ := mk.surjective i
    cases o <;> cases i
    exacts [.inl rfl, .inr (.inl rfl), .inr (.inr (.inr rfl)), .inr (.inr (.inl rfl))]
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨1, one_smul _ _⟩, ⟨(.positive, mk .negative), rfl⟩,
      ⟨(.negative, mk .negative), rfl⟩, ⟨(.negative, mk .positive), rfl⟩]

/-! ### Flipping part of the scope

Inner negation complements the whole scope. A set `N` of individuals acts on a quantifier by
complementing the scope within `N` only, taking `Q` to the quantifier that holds of `B` when `Q`
holds of `N ∆ B`. These are the actions of the sets under symmetric difference, and inner negation
is the action of the whole universe. -/

theorem mk_toBoolRing_vadd_apply (N B : Set α) (Q : Quantifier α) :
    (DomAddAct.mk (toBoolRing N) +ᵥ Q) B = Q (symmDiff N B) := rfl

/-- Inner negation is the flip of the whole scope. -/
theorem mk_toBoolRing_univ_vadd (Q : Quantifier α) :
    DomAddAct.mk (toBoolRing (Set.univ : Set α)) +ᵥ Q = Q.innerNeg :=
  innerNeg_eq_symmDiff_univ.symm

/-! ### The restrictions under the actions

Each of the three actions leaves the restriction of a quantifier unchanged. A flip within `N`
exchanges the positive and the negative restriction on `N`. Flipping a single individual fixes a
quantifier exactly when the quantifier does not depend on that individual. -/

section Restriction

open Set

variable (Q : Quantifier α) (N : Set α) {x : α}

@[simp] theorem restriction_smul (p : Polarity) : (p • Q).restriction = Q.restriction := by
  cases p
  exacts [rfl, restriction_compl]

@[simp] theorem restriction_mk_smul (p : Polarity) :
    (DomMulAct.mk p • Q).restriction = Q.restriction := by
  cases p
  · rfl
  · exact (congrArg restriction (mk_negative_smul Q)).trans <| by
      rw [innerNeg_eq_symmDiff_univ]; exact restriction_symmDiff univ

@[simp] theorem restriction_vadd :
    (DomAddAct.mk (toBoolRing N) +ᵥ Q).restriction = Q.restriction :=
  restriction_symmDiff N

theorem positiveRestriction_vadd :
    (DomAddAct.mk (toBoolRing N) +ᵥ Q).positiveRestriction =
      Q.positiveRestriction \ N ∪ Q.negativeRestriction ∩ N :=
  positiveRestriction_symmDiff N

theorem negativeRestriction_vadd :
    (DomAddAct.mk (toBoolRing N) +ᵥ Q).negativeRestriction =
      Q.negativeRestriction \ N ∪ Q.positiveRestriction ∩ N :=
  negativeRestriction_symmDiff N

/-- Flipping one individual fixes a quantifier if and only if the quantifier lives on the other
individuals. -/
theorem mk_toBoolRing_singleton_vadd_eq_iff :
    DomAddAct.mk (toBoolRing ({x} : Set α)) +ᵥ Q = Q ↔ Q.LivesOn {x}ᶜ := by
  have e (B : Set α) : {x}ᶜ ∩ symmDiff {x} B = {x}ᶜ ∩ B := by
    ext y; simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_symmDiff]; tauto
  constructor
  · intro h B
    by_cases hx : x ∈ B
    · have := congrFun h ({x}ᶜ ∩ B)
      have e' : symmDiff {x} ({x}ᶜ ∩ B) = B := by
        ext y; simp only [mem_symmDiff, mem_inter_iff, mem_compl_iff, mem_singleton_iff]
        by_cases hy : y = x
        · subst hy; tauto
        · tauto
      rw [mk_toBoolRing_vadd_apply, e'] at this
      exact iff_of_eq this
    · rw [show {x}ᶜ ∩ B = B from inter_eq_right.2 fun y hy hyx ↦ hx (hyx ▸ hy)]
  · intro h
    funext B
    rw [mk_toBoolRing_vadd_apply]
    exact propext ((h _).trans ((congrArg Q (e B)).to_iff.trans (h B).symm))

/-- On a finite universe, flipping one individual fixes a quantifier if and only if the
individual is outside the restriction of the quantifier. -/
theorem mk_toBoolRing_singleton_vadd_eq_iff_notMem [Finite α] :
    DomAddAct.mk (toBoolRing ({x} : Set α)) +ᵥ Q = Q ↔ x ∉ Q.restriction :=
  (mk_toBoolRing_singleton_vadd_eq_iff Q).trans
    ⟨fun h hx ↦ h.restriction_subset hx rfl,
      fun hx ↦ (livesOn_restriction (Q := Q)).mono (subset_compl_singleton_iff.2 hx)⟩

end Restriction

end Quantifier

namespace Polarity.MonoBy

open Quantifier DomMulAct

variable {α : Type*} {Q : Quantifier α} {s : Polarity}

/-- If `Q` is directed by `s`, then `o • Q` is directed by `o * s`. -/
protected theorem smul (h : s.MonoBy Q) (o : Polarity) : (o * s).MonoBy (o • Q) := by
  cases o
  · exact h
  · cases s
    exacts [fun _ _ hB hn hq ↦ hn (h hB hq), fun _ _ hB hn hq ↦ hn (h hB hq)]

/-- If `Q` is directed by `s`, then `mk i • Q` is directed by `i * s`. -/
protected theorem mk_smul (h : s.MonoBy Q) (i : Polarity) : (i * s).MonoBy (mk i • Q) := by
  cases i
  · exact h
  · cases s
    exacts [fun _ _ hB ↦ h (Set.compl_subset_compl.2 hB),
      fun _ _ hB ↦ h (Set.compl_subset_compl.2 hB)]

/-- If `Q` is directed by `s`, then `o • mk i • Q` is directed by `o * i * s`. In particular the
dual of a monotone quantifier is monotone. -/
protected theorem smul_mk_smul (h : s.MonoBy Q) (o i : Polarity) :
    (o * i * s).MonoBy (o • mk i • Q) := by
  rw [mul_assoc]
  exact (h.mk_smul i).smul o

end Polarity.MonoBy
