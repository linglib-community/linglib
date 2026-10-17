module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Presupposition.Trigger
public import Linglib.Semantics.Attitudes.Basic
public import Linglib.Logic.Modal.Basic

/-!
# Doxastic attitude semantics

Accessibility semantics for doxastic attitude verbs (*believe*, *know*, *think*) in Hintikka's
tradition: `w ~[R x] w'` reads "`w'` is compatible with what `x` believes or knows in `w`", and
⟦x believes p⟧(w) is the relational box `□[R x] p w`, so closure under known implication is the
K axiom `ModalLogic.box_K`.

A `DoxasticPredicate` pairs an accessibility relation with a veridicality value and a factivity
class. Applied to a complement it is a trivalent proposition (`DoxasticPredicate.sentence`) that
presupposes the complement when the predicate is factive and asserts the box, together with the
complement when it is veridical. Veridicality is thus an entailment
(`veridical_entails_complement`) and factivity a presupposition, which a context admits only if it
entails the complement (`support_sentence`). Over reflexive accessibility both requirements are
redundant by the T axiom (`holdsAt_iff_box`).

## References

* [hintikka-1962]
-/

@[expose] public section

namespace Doxastic

open ModalLogic Presupposition SetRel

variable {W E : Type*}

/-- A veridical verb requires its complement `p` to hold at `w`, and a non-veridical one requires
nothing. -/
def VeridicalityHolds (v : Veridicality) (p : W → Prop) (w : W) : Prop :=
  match v with
  | .veridical => p w
  | .nonVeridical => True

instance (v : Veridicality) (p : W → Prop) [DecidablePred p] (w : W) :
    Decidable (VeridicalityHolds v p w) :=
  match v with
  | .veridical => inferInstanceAs (Decidable (p w))
  | .nonVeridical => inferInstanceAs (Decidable True)

/-- A doxastic attitude predicate is an accessibility relation for each attitude holder, with a
veridicality value and a factivity class. -/
structure DoxasticPredicate (W E : Type*) where
  /-- `w ~[access x] w'` when `w'` is compatible with the attitude of `x` in `w`. -/
  access : E → SetRel W W
  /-- Whether the predicate entails its complement. -/
  veridicality : Veridicality
  /-- The factivity class of a predicate that presupposes its complement, `none` otherwise. -/
  factivity : Option Factivity := none

namespace DoxasticPredicate

variable (V : DoxasticPredicate W E) (agent : E) (p : W → Prop) (w : W)

open Classical in
/-- Applied to a holder and a complement, the predicate is a trivalent proposition that
presupposes the complement if the predicate is factive and asserts the box, together with the
complement if it is veridical. -/
noncomputable def sentence : W → SignType :=
  {w | ∀ _ ∈ V.factivity, p w}.indicator fun w ↦
    SignType.ofProp (VeridicalityHolds V.veridicality p w ∧ □[V.access agent] p w)

/-- ⟦x V that p⟧(w) is true when `sentence` is. -/
def HoldsAt : Prop := V.sentence agent p w = 1

theorem holdsAt_iff :
    V.HoldsAt agent p w ↔ (∀ _ ∈ V.factivity, p w) ∧ VeridicalityHolds V.veridicality p w ∧
      □[V.access agent] p w := by
  simp [HoldsAt, sentence]

/-- A factive predicate is defined exactly where its complement is true, and a non-factive one
everywhere. -/
theorem support_sentence :
    Function.support (V.sentence agent p) = {w | ∀ _ ∈ V.factivity, p w} := by
  ext w
  simp [sentence, -SignType.ofProp_and]

instance [Fintype W] [∀ v, Decidable (w ~[V.access agent] v)] [DecidablePred p] :
    Decidable (V.HoldsAt agent p w) :=
  decidable_of_iff _ (V.holdsAt_iff agent p w).symm

variable {V agent p w}

/-- A veridical predicate entails its complement, so if `x` knows `p` at `w`, then `p w`. -/
theorem veridical_entails_complement (hV : V.veridicality = .veridical)
    (h : V.HoldsAt agent p w) : p w := by
  rw [holdsAt_iff, hV] at h
  exact h.2.1

/-- Over reflexive accessibility the veridicality and factivity requirements are redundant, and
the predicate holds exactly when its complement is true at every accessible world. -/
theorem holdsAt_iff_box [(V.access agent).IsRefl] :
    V.HoldsAt agent p w ↔ □[V.access agent] p w := by
  rw [holdsAt_iff]
  refine ⟨fun h ↦ h.2.2, fun h ↦ ⟨fun _ _ ↦ box_T h, ?_, h⟩⟩
  cases V.veridicality
  exacts [box_T h, trivial]

end DoxasticPredicate

end Doxastic
