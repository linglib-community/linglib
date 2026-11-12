module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Presupposition.Trigger
public import Linglib.Logic.Modal.Basic
public import Linglib.Semantics.Attitudes.Basic

/-!
# Doxastic attitude semantics

Accessibility semantics for doxastic attitude verbs (*believe*, *know*, *think*) in Hintikka's
tradition: `w ~[R x] w'` reads "`w'` is compatible with what `x` believes or knows in `w`", and
⟦x believes p⟧(w) is the relational box `□[R x] p w`, so closure under known implication is the
K axiom `ModalLogic.box_K`. A `DoxasticPredicate` pairs an accessibility relation with a
factivity class; applied to a complement it presupposes the complement when factive, which a
context admits only if it entails the complement (`compl_gapExt_sentence`), and asserts the box. A
predicate is veridical when it entails its complement (`IsVeridical`), which it does exactly when
it is factive or its accessibility is reflexive for every holder (`isVeridical_iff`). A verb's entry
records its factivity and whether its alternatives are epistemic, reflexive in every model, or
doxastic, and it is veridical exactly when
[every denotation of that kind is](##Doxastic.isVeridical_forall_iff).

A predicate can also entail its complement without presupposing it. The
[veridical counterpart](##Doxastic.DoxasticPredicate.veridical) of a predicate asserts the
complement at the world of evaluation; it is
[true where the factive is](##Doxastic.DoxasticPredicate.posExt_sentence_veridical), and the
factive is [false only where the complement is true
besides](##Doxastic.DoxasticPredicate.negExt_sentence_eq_inter), so the two analyses of *know*
part under negation.

## Implementation notes

Veridicality is derived, not stored: a predicate that asserts its complement besides the box is
one whose accessibility is closed under reflexivity, since `□[R ∪ SetRel.id] p w` is
`□[R] p w ∧ p w` (`ModalLogic.box_union`, `ModalLogic.box_id`). The entry fixes the factivity
class of its denotation and, when its alternatives are epistemic, that the accessibility is
reflexive; doxastic alternatives impose nothing, so a non-factive predicate over them has a
denotation that is not veridical, the empty accessibility.

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

/-- The predicate is factive when it carries a factivity class. -/
def IsFactive : Prop := V.factivity ≠ none

instance : Decidable V.IsFactive := inferInstanceAs (Decidable (_ ≠ _))

open Classical in
/-- Applied to a holder and a complement, the predicate is a trivalent proposition that
presupposes the complement if the predicate is factive and asserts the box. -/
noncomputable def sentence : W → Trivalent :=
  Trivalent.condEvent (fun w ↦ V.IsFactive → p w) (□[V.access agent] p)

/-- ⟦x V that p⟧(w) is true when `sentence` is. -/
def HoldsAt : Prop := V.sentence agent p w = .true

theorem holdsAt_iff : V.HoldsAt agent p w ↔ (V.IsFactive → p w) ∧ □[V.access agent] p w := by
  simp [HoldsAt, sentence]

theorem posExt_sentence :
    Trivalent.posExt (V.sentence agent p) = {w | (V.IsFactive → p w) ∧ □[V.access agent] p w} := by
  simp [sentence]

theorem negExt_sentence :
    Trivalent.negExt (V.sentence agent p) =
      {w | (V.IsFactive → p w) ∧ ¬ □[V.access agent] p w} := by
  simp [sentence]

theorem compl_gapExt_sentence :
    (Trivalent.gapExt (V.sentence agent p))ᶜ = {w | V.IsFactive → p w} := by
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
  exact ⟨And.right, fun h ↦ ⟨fun _ ↦ box_T h, h⟩⟩

/-- A predicate is veridical exactly when it is factive or reflexive in its accessibility for
every holder. -/
theorem isVeridical_iff : V.IsVeridical ↔ V.IsFactive ∨ ∀ a, (V.access a).IsRefl := by
  refine ⟨fun h ↦ or_iff_not_imp_left.2 fun hF a ↦ ⟨fun v ↦ h a (v ~[V.access a] ·) v ?_⟩, ?_⟩
  · exact (holdsAt_iff ..).2 ⟨fun hf ↦ absurd hf hF, fun _ ↦ id⟩
  · rintro (hF | hR) a q v h
    · exact ((holdsAt_iff ..).1 h).1 hF
    · have := hR a
      exact box_T ((holdsAt_iff ..).1 h).2

/-! ### Asserting the complement

A predicate can entail its complement without presupposing it, by asserting it at the world of
evaluation. Such a predicate is true where the factive over the same alternatives is, and the two
part under negation: the factive is false only where the complement is true, and undefined where
it is false, while its veridical counterpart is false there. -/

variable (V) in
/-- The veridical counterpart of a predicate asserts the complement where a factive presupposes
it: the world of evaluation joins the holder's alternatives and nothing is presupposed. -/
def veridical : DoxasticPredicate W E where
  access a := V.access a ∪ SetRel.id

theorem not_isFactive_veridical : ¬ V.veridical.IsFactive := fun h ↦ h rfl

theorem holdsAt_veridical_iff :
    V.veridical.HoldsAt agent p w ↔ □[V.access agent] p w ∧ p w := by
  rw [holdsAt_iff, and_iff_right fun h ↦ absurd h not_isFactive_veridical]
  exact (box_union _).trans (and_congr_right' box_id)

theorem isVeridical_veridical : V.veridical.IsVeridical :=
  fun _ _ _ h ↦ (holdsAt_veridical_iff.1 h).2

/-- The veridical counterpart presupposes nothing. -/
theorem gapExt_sentence_veridical : Trivalent.gapExt (V.veridical.sentence agent p) = ∅ := by
  rw [← compl_compl (Trivalent.gapExt _), compl_gapExt_sentence]
  simp [not_isFactive_veridical]

/-- A factive predicate and its veridical counterpart are true at the same worlds. -/
theorem posExt_sentence_veridical (hV : V.IsFactive) :
    Trivalent.posExt (V.veridical.sentence agent p) = Trivalent.posExt (V.sentence agent p) := by
  ext w
  exact holdsAt_veridical_iff.trans
    ((holdsAt_iff ..).trans ⟨fun h ↦ ⟨h.2, h.1 hV⟩, fun h ↦ ⟨fun _ ↦ h.2, h.1⟩⟩).symm

/-- A factive predicate is false at the worlds where its veridical counterpart is false and the
complement is true. -/
theorem negExt_sentence_eq_inter (hV : V.IsFactive) :
    Trivalent.negExt (V.sentence agent p) =
      Trivalent.negExt (V.veridical.sentence agent p) ∩ {w | p w} := by
  ext w
  rw [Set.mem_inter_iff, negExt_sentence, negExt_sentence]
  exact ⟨fun h ↦ ⟨⟨fun hf ↦ absurd hf not_isFactive_veridical,
      fun hb ↦ h.2 ((box_union _).1 hb).1⟩, h.1 hV⟩,
    fun h ↦ ⟨fun _ ↦ h.2, fun hb ↦ h.1.2 ((box_union _).2 ⟨hb, box_id.2 h.2⟩)⟩⟩

end DoxasticPredicate

/-- A doxastic predicate of factivity class `fac` over alternatives `b` is veridical under every
denotation of its kind, of that class and reflexive when `b` is epistemic, exactly when the
attitude `.doxastic b` is veridical. -/
theorem isVeridical_forall_iff (fac : Option Factivity) (b : Alternatives) :
    (∀ (W E : Type) (V : DoxasticPredicate W E), V.factivity = fac →
      (b = .epistemic → ∀ a, (V.access a).IsRefl) → V.IsVeridical) ↔
      (Attitude.doxastic b).IsVeridical fac := by
  refine ⟨fun h ↦ ?_, fun h W E V hf hr ↦ ?_⟩
  · by_contra hn
    simp only [Attitude.IsVeridical, ne_eq, not_or, not_not] at hn
    exact h Unit Unit ⟨fun _ ↦ ∅, none⟩ hn.1.symm (fun hb ↦ absurd hb hn.2) () (fun _ ↦ False) ()
      ((DoxasticPredicate.holdsAt_iff ..).2
        ⟨fun hF ↦ absurd rfl hF, fun _ hv ↦ absurd hv (Set.notMem_empty _)⟩)
  · rw [DoxasticPredicate.isVeridical_iff]
    exact h.imp (fun hfac hn ↦ hfac (hf ▸ hn)) hr

end Doxastic
