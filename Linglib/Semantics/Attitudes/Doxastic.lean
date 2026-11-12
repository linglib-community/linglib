module

public import Linglib.Semantics.Presupposition.Factive
public import Linglib.Semantics.Presupposition.Trigger
public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Attitudes.Basic

/-!
# Doxastic attitude semantics

Accessibility semantics for doxastic attitude verbs (*believe*, *know*, *think*) in Hintikka's
tradition: `w ~[R] w'` reads "`w'` is compatible with what the holder believes or knows in `w`",
and ⟦x believes p⟧(w) is the relational box `□[R] p w`, so closure under known implication is the
K axiom `ModalLogic.box_K`. A verb entails its complement in one of three ways. Its alternatives
may be epistemic, among which the world of evaluation always is, so that the box is veridical
(`ModalLogic.box_T`). It may assert the complement beside the box, which is the box over the
alternatives with the world of evaluation added (`ModalLogic.box_union`, `ModalLogic.box_id`). Or
it may presuppose the complement, as `Presupposition.factive` does, which is
[true at the same worlds](##Doxastic.posExt_factive_box). A verb's entry records its factivity and
whether its alternatives are epistemic or doxastic, and it is veridical exactly when
[every denotation of that kind is](##Doxastic.isVeridical_forall_iff).

## Implementation notes

Veridicality is derived, not stored. The entry fixes whether its denotation presupposes the
complement and, when its alternatives are epistemic, that the accessibility is reflexive; doxastic
alternatives impose nothing, so a non-factive predicate over them has a denotation that is not
veridical, the empty accessibility.

## References

* [hintikka-1962]
-/

@[expose] public section

namespace Doxastic

open ModalLogic Presupposition SetRel

variable {W : Type*}

/-- A factive doxastic predicate is true where the complement holds throughout the alternatives
with the world of evaluation added. -/
theorem posExt_factive_box (R : SetRel W W) (p : W → Prop) :
    Trivalent.posExt (factive □[R] p) = {w | □[R ∪ SetRel.id] p w} := by
  ext w
  rw [posExt_factive]
  exact ((box_union _).trans (and_congr_right' box_id)).symm

/-- A doxastic predicate of factivity class `fac` over alternatives `b` entails its complement
under every denotation of its kind, which presupposes the complement when `fac` is a class and
is reflexive when `b` is epistemic, exactly when the attitude `.doxastic b` is veridical. -/
theorem isVeridical_forall_iff (fac : Option Factivity) (b : Alternatives) :
    (∀ (W : Type) (R : SetRel W W), (b = .epistemic → R.IsRefl) →
      ∀ (p : W → Prop) (w : W), (fac ≠ none → p w) → □[R] p w → p w) ↔
      (Attitude.doxastic b).IsVeridical fac := by
  refine ⟨fun h ↦ ?_, fun h W R hr p w hf hb ↦ ?_⟩
  · by_contra hn
    simp only [Attitude.IsVeridical, ne_eq, not_or, not_not] at hn
    exact h Unit ∅ (fun hb ↦ absurd hb hn.2) (fun _ ↦ False) () (fun hf ↦ absurd hn.1 hf)
      fun _ hv ↦ absurd hv (Set.notMem_empty _)
  · rcases h with hfac | hb'
    · exact hf hfac
    · have := hr hb'
      exact box_T hb

end Doxastic
