module

public import Studies.DaleReiter1995

/-!
# Chen and van Deemter (2023): Varieties of Specification

This file formalizes the set-theoretic account of over- and under-specification in
[chen-van-deemter-2023]. A description is a bag of attribute–value pairs over the knowledge
base of [dale-reiter-1995], and it is distinguishing when it holds of the referent and of no
distractor. An over-specification is a distinguishing description that is not minimal, and it
is real, numerical, nominal or duplicate-attribute according to which of its occurrences are
superfluous; an under-specification, whose extension in the setting properly contains the
referent, is mixed when some occurrence can be dropped without changing the extension and pure
otherwise; a wrong description has a property false of the referent. The paper's four theorems
hold for any knowledge base and nonempty set of distractors, and the worked examples of its
running scene are classified.

## Implementation notes

* Descriptions are multisets so that a property can occur twice. On a `Finset` description
  `Distinguishing` is Dale and Reiter's (`distinguishing_val_iff`).
* A superfluous occurrence is one of a distinguishing description, as the paper defines it. The
  remark under its nominal over-specification that distinguishing need not be required
  separately holds only for properties true of the referent, so the definitions here carry it.
* Minimality counts property occurrences, as `MinimalFor` on the multiset's cardinality among
  distinguishing descriptions.
* The theorem that a duplicate-attribute over-specification is real or nominal uses that a
  knowledge base assigns one value per attribute, so a distinguishing description has one type.
* The scenes carry the objects and colours of the paper's two figures. Sizes and orientations,
  which the figures do not label, are as the text's classifications require: only the target of
  the first scene is large, and in the second every small object is green and the target and one
  other desk face front.

## References

* [chen-van-deemter-2023]
* [dale-reiter-1995]
-/

@[expose] public section

namespace ChenVanDeemter2023

open DaleReiter1995 Multiset

variable {E A V : Type*}

/-- A description, a bag of attribute–value pairs. -/
abbrev Description (A V : Type*) := Multiset (A × V)

section Basic

variable (kb : KB E A V) (r : E) (C : Finset E) (D : Description A V)

/-- Every pair of the description holds of the entity. -/
def extension (x : E) : Prop := ∀ p ∈ D, Applies kb x p

instance [DecidableEq V] (x : E) : Decidable (extension kb D x) := by
  unfold extension; infer_instance

/-- The description holds of the referent and of no distractor. -/
abbrev Distinguishing : Prop := Distinguishes (extension kb) C r D

/-- A distinguishing description with the fewest property occurrences. -/
def IsMinimal : Prop := MinimalFor (Distinguishing kb r C) card D

/-- A distinguishing description that is not minimal. -/
def OverSpecified : Prop := Distinguishing kb r C D ∧ ¬ IsMinimal kb r C D

/-- The description holds of the referent and of some distractor. -/
def UnderSpecified : Prop := extension kb D r ∧ ∃ c ∈ C, extension kb D c

instance [DecidableEq V] : Decidable (UnderSpecified kb r C D) := by
  unfold UnderSpecified; infer_instance

/-- Some property is false of the referent. -/
def Wrong : Prop := ∃ p ∈ D, ¬ Applies kb r p

instance [DecidableEq V] : Decidable (Wrong kb r D) := by
  unfold Wrong; exact Multiset.decidableExistsMultiset

variable {kb r C D}

/-- On a set of pairs the notion is Dale and Reiter's. -/
theorem distinguishing_val_iff (hC : C.Nonempty) {L : DaleReiter1995.Description A V} :
    Distinguishing kb r C L.val ↔ DaleReiter1995.Distinguishing kb r C L := by
  rw [Distinguishing, distinguishes_prop_iff hC, DaleReiter1995.distinguishing_iff]
  simp [extension]

theorem not_distinguishing_zero (hC : C.Nonempty) : ¬ Distinguishing kb r C 0 :=
  fun h ↦ ((distinguishes_prop_iff hC).1 h).2 _ hC.choose_spec
    fun _ h ↦ (Multiset.notMem_zero _ h).elim

theorem Distinguishing.extension_referent (hC : C.Nonempty) (h : Distinguishing kb r C D) :
    extension kb D r :=
  ((distinguishes_prop_iff hC).1 h).1

theorem Distinguishing.not_extension (hC : C.Nonempty) (h : Distinguishing kb r C D) {c : E}
    (hc : c ∈ C) : ¬ extension kb D c :=
  ((distinguishes_prop_iff hC).1 h).2 c hc

/-- A distinguishing description with one occurrence is minimal. -/
theorem isMinimal_of_card_eq_one (hC : C.Nonempty) (h : Distinguishing kb r C D)
    (h1 : card D = 1) : IsMinimal kb r C D :=
  minimalFor_iff_forall_lt.2 ⟨h, fun D' hlt ↦ by
    obtain rfl := card_eq_zero.1 (Nat.lt_one_iff.1 (h1 ▸ hlt))
    exact not_distinguishing_zero hC⟩

/-- A knowledge base assigns one value per attribute. -/
theorem Applies.snd_eq {x : E} {p q : A × V} (hp : Applies kb x p) (hq : Applies kb x q)
    (h : p.1 = q.1) : p.2 = q.2 := by
  unfold Applies at hp hq
  rw [h] at hp
  exact Option.some_injective _ (hp.symm.trans hq)

theorem UnderSpecified.not_wrong (h : UnderSpecified kb r C D) : ¬ Wrong kb r D :=
  fun ⟨p, hp, hpr⟩ ↦ hpr (h.1 p hp)

end Basic

section Kinds

variable [DecidableEq A] [DecidableEq V] (kb : KB E A V) (t : A) (r : E) (C : Finset E)
  (D : Description A V)

/-- An occurrence of a distinguishing description whose removal leaves it distinguishing. -/
def Superfluous (p : A × V) : Prop :=
  Distinguishing kb r C D ∧ p ∈ D ∧ Distinguishing kb r C (D.erase p)

instance (p : A × V) : Decidable (Superfluous kb r C D p) := by
  unfold Superfluous; infer_instance

/-- Some property other than the type is superfluous. -/
def RealOverSpecified : Prop := ∃ p ∈ D, p.1 ≠ t ∧ Superfluous kb r C D p

/-- A distinguishing description with no superfluous occurrence that is not minimal. -/
def NumericallyOverSpecified : Prop :=
  Distinguishing kb r C D ∧ (∀ p ∈ D, ¬ Superfluous kb r C D p) ∧ ¬ IsMinimal kb r C D

/-- The type is superfluous and no other property is. -/
def NominallyOverSpecified : Prop :=
  ∃ p ∈ D, p.1 = t ∧ Superfluous kb r C D p ∧ ∀ q ∈ D, q ≠ p → ¬ Superfluous kb r C D q

/-- A property occurs twice and is superfluous. -/
def DuplicateOverSpecified : Prop := ∃ p ∈ D, 2 ≤ D.count p ∧ Superfluous kb r C D p

/-- An under-specification with an occurrence whose removal leaves its extension on the
setting unchanged; the referent stays in the extension by under-specification, so only the
distractors are checked. -/
def Mixed : Prop :=
  UnderSpecified kb r C D ∧ ∃ p ∈ D, ∀ c ∈ C, extension kb (D.erase p) c → extension kb D c

/-- An under-specification that is not mixed. -/
def PurelyUnderSpecified : Prop := UnderSpecified kb r C D ∧ ¬ Mixed kb r C D

instance : Decidable (RealOverSpecified kb t r C D) := by
  unfold RealOverSpecified; exact Multiset.decidableExistsMultiset

instance : Decidable (NominallyOverSpecified kb t r C D) := by
  unfold NominallyOverSpecified; exact Multiset.decidableExistsMultiset

instance : Decidable (DuplicateOverSpecified kb r C D) := by
  unfold DuplicateOverSpecified; exact Multiset.decidableExistsMultiset

instance : Decidable (Mixed kb r C D) := by
  unfold Mixed; exact instDecidableAnd (dq := Multiset.decidableExistsMultiset)

instance : Decidable (PurelyUnderSpecified kb r C D) := by
  unfold PurelyUnderSpecified; infer_instance

variable {kb t r C D}

theorem Superfluous.not_isMinimal {p : A × V} (h : Superfluous kb r C D p) :
    ¬ IsMinimal kb r C D :=
  fun hm ↦ hm.not_prop_of_lt (card_erase_lt_of_mem h.2.1) h.2.2

/-- Every kind of over-specification is distinguishing. -/
theorem theorem1 :
    (IsMinimal kb r C D → Distinguishing kb r C D) ∧
      (RealOverSpecified kb t r C D → Distinguishing kb r C D) ∧
      (NumericallyOverSpecified kb r C D → Distinguishing kb r C D) ∧
      (NominallyOverSpecified kb t r C D → Distinguishing kb r C D) ∧
      (DuplicateOverSpecified kb r C D → Distinguishing kb r C D) :=
  ⟨MinimalFor.prop, fun ⟨_, _, _, h⟩ ↦ h.1, And.left, fun ⟨_, _, _, h, _⟩ ↦ h.1,
    fun ⟨_, _, _, h⟩ ↦ h.1⟩

/-- A distinguishing description is neither mixed, purely under-specified nor wrong. -/
theorem theorem2 (hC : C.Nonempty) (h : Distinguishing kb r C D) :
    ¬ Mixed kb r C D ∧ ¬ PurelyUnderSpecified kb r C D ∧ ¬ Wrong kb r D :=
  ⟨fun ⟨⟨_, _, hc, hce⟩, _⟩ ↦ h.not_extension hC hc hce,
    fun ⟨⟨_, _, hc, hce⟩, _⟩ ↦ h.not_extension hC hc hce,
    fun ⟨p, hp, hpr⟩ ↦ hpr (h.extension_referent hC p hp)⟩

/-- The seven kinds of description exclude one another. -/
theorem theorem3 (hC : C.Nonempty) :
    List.Pairwise (fun P Q : Description A V → Prop ↦ ∀ D, ¬ (P D ∧ Q D))
      [IsMinimal kb r C, RealOverSpecified kb t r C, NumericallyOverSpecified kb r C,
        NominallyOverSpecified kb t r C, Mixed kb r C, PurelyUnderSpecified kb r C,
        Wrong kb r] := by
  have dist : ∀ D : Description A V, _ := fun D ↦ @theorem1 E A V _ _ kb t r C D
  have under : ∀ D, Distinguishing kb r C D →
      ¬ Mixed kb r C D ∧ ¬ PurelyUnderSpecified kb r C D ∧ ¬ Wrong kb r D :=
    fun _ ↦ theorem2 hC
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))))
  all_goals simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true]
  · exact ⟨fun D ⟨hm, _, _, _, hs⟩ ↦ hs.not_isMinimal hm, fun D ⟨hm, _, _, hn⟩ ↦ hn hm,
      fun D ⟨hm, _, _, _, hs, _⟩ ↦ hs.not_isMinimal hm,
      fun D ⟨hm, h⟩ ↦ (under D ((dist D).1 hm)).1 h,
      fun D ⟨hm, h⟩ ↦ (under D ((dist D).1 hm)).2.1 h,
      fun D ⟨hm, h⟩ ↦ (under D ((dist D).1 hm)).2.2 h⟩
  · exact ⟨fun D ⟨⟨p, hp, _, hs⟩, _, hn, _⟩ ↦ hn p hp hs,
      fun D ⟨⟨p, hp, hpt, hs⟩, q, hq, hqt, _, hn⟩ ↦ hn p hp (fun h ↦ hpt (h ▸ hqt)) hs,
      fun D ⟨hr, h⟩ ↦ (under D ((dist D).2.1 hr)).1 h,
      fun D ⟨hr, h⟩ ↦ (under D ((dist D).2.1 hr)).2.1 h,
      fun D ⟨hr, h⟩ ↦ (under D ((dist D).2.1 hr)).2.2 h⟩
  · exact ⟨fun D ⟨⟨_, hn, _⟩, p, hp, _, hs, _⟩ ↦ hn p hp hs,
      fun D ⟨hn, h⟩ ↦ (under D ((dist D).2.2.1 hn)).1 h,
      fun D ⟨hn, h⟩ ↦ (under D ((dist D).2.2.1 hn)).2.1 h,
      fun D ⟨hn, h⟩ ↦ (under D ((dist D).2.2.1 hn)).2.2 h⟩
  · exact ⟨fun D ⟨hn, h⟩ ↦ (under D ((dist D).2.2.2.1 hn)).1 h,
      fun D ⟨hn, h⟩ ↦ (under D ((dist D).2.2.2.1 hn)).2.1 h,
      fun D ⟨hn, h⟩ ↦ (under D ((dist D).2.2.2.1 hn)).2.2 h⟩
  · exact ⟨fun D ⟨hm, _, hp⟩ ↦ hp hm, fun D ⟨hm, hw⟩ ↦ hm.1.not_wrong hw⟩
  · exact fun D ⟨hp, hw⟩ ↦ hp.1.not_wrong hw

/-- A duplicate-attribute over-specification is real or nominal, since the type occurrences of a
distinguishing description are one pair. -/
theorem theorem4 (hC : C.Nonempty) (h : DuplicateOverSpecified kb r C D) :
    RealOverSpecified kb t r C D ∨ NominallyOverSpecified kb t r C D := by
  obtain ⟨p, hp, -, hs⟩ := h
  by_cases hpt : p.1 = t
  · by_cases hq : ∃ q ∈ D, q ≠ p ∧ Superfluous kb r C D q
    · obtain ⟨q, hq, hqp, hqs⟩ := hq
      refine .inl ⟨q, hq, fun hqt ↦ hqp ?_, hqs⟩
      have hr := hs.1.extension_referent hC
      exact Prod.ext (hqt.trans hpt.symm)
        (Applies.snd_eq (hr q hq) (hr p hp) (hqt.trans hpt.symm))
    · exact .inr ⟨p, hp, hpt, hs, fun q hq' hqp hqs ↦ hq ⟨q, hq', hqp, hqs⟩⟩
  · exact .inl ⟨p, hp, hpt, hs⟩

end Kinds

/-! ### The scenes of the examples -/

/-- The objects of the two scenes. -/
inductive Obj
  | greyDesk | redSofa | greenChair | greenSofa | blueChair | greenFan | greenDesk
  | greyChair | largeGreenChair | smallGreenChair | targetDesk | largeGreenDesk | smallGreenDesk
  | greyDesk'
  deriving DecidableEq, Repr

/-- The attributes, with `type` the head noun. -/
inductive Attr
  | type | size | colour | orientation
  deriving DecidableEq, Repr

/-- The values. -/
inductive Value
  | chair | sofa | desk | fan | large | small | grey | red | green | blue | front | side
  deriving DecidableEq, Repr

/-- The first scene, a large green chair among a grey desk, a red sofa, a green sofa, a blue
chair, a green fan and a green desk. -/
def scene₁ : KB Obj Attr Value
  | .greenChair, .type => some .chair
  | .greenChair, .size => some .large
  | .greenChair, .colour => some .green
  | .greyDesk, .type => some .desk
  | .greyDesk, .size => some .small
  | .greyDesk, .colour => some .grey
  | .redSofa, .type => some .sofa
  | .redSofa, .size => some .small
  | .redSofa, .colour => some .red
  | .greenSofa, .type => some .sofa
  | .greenSofa, .size => some .small
  | .greenSofa, .colour => some .green
  | .blueChair, .type => some .chair
  | .blueChair, .size => some .small
  | .blueChair, .colour => some .blue
  | .greenFan, .type => some .fan
  | .greenFan, .size => some .small
  | .greenFan, .colour => some .green
  | .greenDesk, .type => some .desk
  | .greenDesk, .size => some .small
  | .greenDesk, .colour => some .green
  | _, _ => none

/-- The distractors of the first scene. -/
def distractors₁ : Finset Obj :=
  {.greyDesk, .redSofa, .greenSofa, .blueChair, .greenFan, .greenDesk}

/-- *The large one* is minimal, *the large green one* a real over-specification, *the green chair*
a numerical one, *the large chair* a nominal one, and *the green chair that has the same colour
as the fan*, which expresses the colour twice, a duplicate-attribute and real one. -/
theorem scene₁_over :
    IsMinimal scene₁ .greenChair distractors₁ {(.size, .large)} ∧
      RealOverSpecified scene₁ .type .greenChair distractors₁
        {(.size, .large), (.colour, .green)} ∧
      NumericallyOverSpecified scene₁ .greenChair distractors₁
        {(.colour, .green), (.type, .chair)} ∧
      NominallyOverSpecified scene₁ .type .greenChair distractors₁
        {(.size, .large), (.type, .chair)} ∧
      DuplicateOverSpecified scene₁ .greenChair distractors₁
        {(.colour, .green), (.type, .chair), (.colour, .green)} ∧
      RealOverSpecified scene₁ .type .greenChair distractors₁
        {(.colour, .green), (.type, .chair), (.colour, .green)} := by
  refine ⟨isMinimal_of_card_eq_one ⟨.blueChair, by decide⟩ (by decide) rfl, by decide,
    ⟨by decide, by decide, fun h ↦ h.not_prop_of_lt (j := {(.size, .large)}) (by decide)
      (by decide)⟩, by decide, by decide, by decide⟩

/-- *The chair* is purely under-specified, and a description calling the green chair blue, as
the paper's *the large blue chair in the middle* does, is wrong. -/
theorem scene₁_under :
    PurelyUnderSpecified scene₁ .greenChair distractors₁ {(.type, .chair)} ∧
      Wrong scene₁ .greenChair {(.size, .large), (.colour, .blue), (.type, .chair)} := by
  decide

/-- The second scene, a small green front-facing desk among a grey chair, a large and a small
green chair, a large green front-facing desk, a small green side-facing desk and a grey desk. -/
def scene₂ : KB Obj Attr Value
  | .targetDesk, .type => some .desk
  | .targetDesk, .size => some .small
  | .targetDesk, .colour => some .green
  | .targetDesk, .orientation => some .front
  | .greyChair, .type => some .chair
  | .greyChair, .size => some .large
  | .greyChair, .colour => some .grey
  | .greyChair, .orientation => some .front
  | .largeGreenChair, .type => some .chair
  | .largeGreenChair, .size => some .large
  | .largeGreenChair, .colour => some .green
  | .largeGreenChair, .orientation => some .front
  | .smallGreenChair, .type => some .chair
  | .smallGreenChair, .size => some .small
  | .smallGreenChair, .colour => some .green
  | .smallGreenChair, .orientation => some .front
  | .largeGreenDesk, .type => some .desk
  | .largeGreenDesk, .size => some .large
  | .largeGreenDesk, .colour => some .green
  | .largeGreenDesk, .orientation => some .front
  | .smallGreenDesk, .type => some .desk
  | .smallGreenDesk, .size => some .small
  | .smallGreenDesk, .colour => some .green
  | .smallGreenDesk, .orientation => some .side
  | .greyDesk', .type => some .desk
  | .greyDesk', .size => some .large
  | .greyDesk', .colour => some .grey
  | .greyDesk', .orientation => some .side
  | _, _ => none

/-- The distractors of the second scene. -/
def distractors₂ : Finset Obj :=
  {.greyChair, .largeGreenChair, .smallGreenChair, .largeGreenDesk, .smallGreenDesk, .greyDesk'}

/-- *The green small desk* is mixed, since every small object is green, and *the front-facing
desk* is purely under-specified. -/
theorem scene₂_under :
    Mixed scene₂ .targetDesk distractors₂ {(.colour, .green), (.size, .small), (.type, .desk)} ∧
      PurelyUnderSpecified scene₂ .targetDesk distractors₂
        {(.orientation, .front), (.type, .desk)} := by
  decide

end ChenVanDeemter2023
