module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Presupposition.Trigger
public import Linglib.Logic.Modal.Basic

/-!
# Doxastic attitude semantics

Accessibility semantics for doxastic attitude verbs (*believe*, *know*, *think*) in Hintikka's
tradition: `w ~[R x] w'` reads "`w'` is compatible with what `x` believes or knows in `w`", and
⟦x believes p⟧(w) is the relational box `□[R x] p w`, so closure under known implication is the
K axiom `ModalLogic.box_K`. A `DoxasticPredicate` pairs an accessibility relation with a
factivity class; applied to a complement it presupposes the complement when factive, which a
context admits only if it entails the complement (`support_sentence`), and asserts the box. A
predicate is veridical when it entails its complement (`IsVeridical`), which it does exactly when
it is factive or its accessibility is reflexive for every holder (`isVeridical_iff`).

## Implementation notes

Veridicality is derived, not stored: a predicate that asserts its complement besides the box is
one whose accessibility is closed under reflexivity, since `□[R ∪ SetRel.id] p w` is
`□[R] p w ∧ p w` (`ModalLogic.box_union`, `ModalLogic.box_id`). The lexical label
`Doxastic.Veridicality` of a verb's `Attitude` records `IsVeridical` of its denotation.

## References

* [hintikka-1962]
-/

@[expose] public section

namespace Doxastic

open ModalLogic Presupposition SetRel

variable {W E : Type*}

/-- A doxastic attitude predicate is an accessibility relation for each attitude holder, with a
factivity class. -/
structure DoxasticPredicate (W E : Type*) where
  /-- `w ~[access x] w'` when `w'` is compatible with the attitude of `x` in `w`. -/
  access : E → SetRel W W
  /-- The factivity class of a predicate that presupposes its complement, `none` otherwise. -/
  factivity : Option Factivity := none

namespace DoxasticPredicate

variable (V : DoxasticPredicate W E) (agent : E) (p : W → Prop) (w : W)

open Classical in
/-- Applied to a holder and a complement, the predicate is a trivalent proposition that
presupposes the complement if the predicate is factive and asserts the box. -/
noncomputable def sentence : W → SignType :=
  {w | ∀ _ ∈ V.factivity, p w}.indicator fun w ↦ SignType.ofProp (□[V.access agent] p w)

/-- ⟦x V that p⟧(w) is true when `sentence` is. -/
def HoldsAt : Prop := V.sentence agent p w = 1

theorem holdsAt_iff :
    V.HoldsAt agent p w ↔ (∀ _ ∈ V.factivity, p w) ∧ □[V.access agent] p w := by
  simp [HoldsAt, sentence]

theorem support_sentence :
    Function.support (V.sentence agent p) = {w | ∀ _ ∈ V.factivity, p w} := by
  ext w
  simp [sentence]

instance [Fintype W] [∀ v, Decidable (w ~[V.access agent] v)] [DecidablePred p] :
    Decidable (V.HoldsAt agent p w) :=
  decidable_of_iff _ (V.holdsAt_iff agent p w).symm

/-- A predicate is veridical when it entails its complement. -/
def IsVeridical : Prop := ∀ a q v, V.HoldsAt a q v → q v

variable {V agent p w}

theorem holdsAt_iff_box [(V.access agent).IsRefl] :
    V.HoldsAt agent p w ↔ □[V.access agent] p w := by
  rw [holdsAt_iff]
  exact ⟨And.right, fun h ↦ ⟨fun _ _ ↦ box_T h, h⟩⟩

/-- A predicate is veridical exactly when it is factive or reflexive in its accessibility for
every holder. -/
theorem isVeridical_iff : V.IsVeridical ↔ V.factivity ≠ none ∨ ∀ a, (V.access a).IsRefl := by
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hF a ↦ ⟨fun v ↦ h a (v ~[V.access a] ·) v ?_⟩, ?_⟩
  · rw [holdsAt_iff, not_not.1 hF]
    exact ⟨nofun, fun _ ↦ id⟩
  · rintro (hF | hR) a q v h
    · obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hF
      exact ((holdsAt_iff ..).1 h).1 f hf
    · have := hR a
      exact box_T ((holdsAt_iff ..).1 h).2

end DoxasticPredicate

end Doxastic
