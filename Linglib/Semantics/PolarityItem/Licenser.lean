/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Presupposition.Strawson
public import Linglib.Semantics.Exhaustification.Antiexhaustive
public import Linglib.Semantics.PolarityItem.Distribution

/-!
# Licensers

A *licenser* is the operator that a construction places over the position of a polarity item. It
is given as a family of operators indexed by whatever the construction leaves open, such as the
model, a restrictor, a bound, or an accessibility relation. A licenser is of one of four kinds. A
*classical* licenser is a map between bounded lattices. A *scalar* licenser is such a map that has
stronger scale-mates. A *Strawsonian* licenser is von Fintel's map into trivalent propositions.
The remaining kind is a *modal* licenser. Following Gajewski, a licenser has a
plain meaning below the exhaustivity operator and a second meaning above it. The meaning above
the operator adds the *direct implicature* of the licenser, which is its exhaustification against
its stronger scale-mates. Only a scalar licenser has a direct implicature.

A licenser has a *negativity*: the greatest strength of negation that it carries and the greatest
that it holds outright. A licenser *admits* a distribution when the context it makes, its
negativity together with whether it licenses free choice, lies in the distribution. The negative
polarity items of a strength are admitted by the licensers that carry it, the positive polarity
items by those that do not hold it, and the free choice items by those that license free choice.
A non-trivial classical licenser admits the positive polarity items of a strength exactly where it
does not admit the negative ones.

## Main definitions

* `PolarityItem.Licenser`: the four kinds of licenser.
* `PolarityItem.Licenser.exhaustified`: the meaning of a licenser above the exhaustivity operator,
  with its direct implicature added.
* `PolarityItem.Licenser.Holds`, `PolarityItem.Licenser.IsStrawsonDE`,
  `PolarityItem.Licenser.IsStrawsonUE`: a strength that a licenser holds outright, and downward
  and upward entailment modulo presupposition.
* `PolarityItem.Licenser.Carries`: a strength of negation that a licenser carries. Von Fintel
  requires the plain meaning to be downward entailing modulo presupposition, and Bylinina and
  Nouwen add that it must not be upward entailing as well. A strength above the monotone decreasing
  one must in addition hold outright of the exhaustified meaning.
* `PolarityItem.Licenser.LicensesByStrengthening`, `PolarityItem.Licenser.LicensesFreeChoice`:
  the two routes of licensing. A downward-entailing licenser licenses by strengthening, after
  Kadmon and Landman, and a modal licenser licenses by free choice, after Chierchia.
* `PolarityItem.Licenser.negativity`, `PolarityItem.Licenser.Admits`: the negativity of a
  licenser, and the distributions that contain the context it makes.

## Main statements

* `PolarityItem.Licenser.licensesByStrengthening_iff`: widening the domain strengthens under a
  licenser exactly when the licenser is downward entailing modulo presupposition.

## Implementation notes

* Licensing is evaluated on the meaning modulo presupposition and with its direct implicature,
  following von Fintel and Gajewski. What excludes a positive polarity item is evaluated on the
  plain meaning, as van der Wouden and Szabolcsi state it. On their account, presuppositional
  operators such as *only* and *regret* rescue a positive polarity item instead of blocking it.
* Gajewski requires only that the exhaustified meaning be downward entailing. Zwarts's strengths
  are retained here, and they agree with Gajewski's condition at the endpoints of the scale.
* A constant map is downward entailing, and a constantly true map is anti-additive. The
  requirement that a licenser of the monotone decreasing strength not be upward entailing as well
  excludes them, since a map that is monotone in both directions modulo presupposition takes a
  single value at comparable arguments where it is defined
  (`Presupposition.isStrawsonUE_and_isStrawsonDE_iff`).
* A question is not a licenser. It is downward entailing only in the domain of a wh-phrase, and
  whether it hosts an item does not follow the strength that the item requires. Van Rooy ties the
  use of an item in a question to the expectations of the questioner, through the entropy of the
  question under the questioner's prior, which is a condition on a use of the question.

## References

* [ladusaw-1979]
* [vanderwouden-1997]
* [szabolcsi-2004]
* [von-fintel-1999]
* [gajewski-2011]
* [zwarts-1998]
* [bylinina-nouwen-2018]
* [icard-2012]
* [kadmon-landman-1993]
* [chierchia-2006]
* [van-rooy-2003a]
-/

@[expose] public section

namespace PolarityItem

open Presupposition Exhaustification

namespace Licenser

/-- A family of operators between bounded lattices, indexed by what a construction leaves open. -/
structure OperatorFamily where
  /-- What the construction leaves open. -/
  Param : Type 1
  /-- The lattice the item's position ranges over. -/
  Dom : Param → Type
  /-- The lattice of the result. -/
  Cod : Param → Type
  /-- The domain is a Boolean algebra. -/
  [boolDom : ∀ p, BooleanAlgebra (Dom p)]
  /-- The codomain is a Boolean algebra. -/
  [boolCod : ∀ p, BooleanAlgebra (Cod p)]
  /-- The operator at each parameter. -/
  op : ∀ p, Dom p → Cod p

attribute [instance] OperatorFamily.boolDom OperatorFamily.boolCod

/-- A family of operators into trivalent propositions, indexed by what a construction leaves
open. -/
structure PresupposingFamily where
  /-- What the construction leaves open. -/
  Param : Type 1
  /-- The lattice the item's position ranges over. -/
  Dom : Param → Type
  /-- The worlds of the trivalent propositions. -/
  W : Param → Type
  /-- The domain is a Boolean algebra. -/
  [boolDom : ∀ p, BooleanAlgebra (Dom p)]
  /-- The operator at each parameter. -/
  op : ∀ p, Dom p → W p → Trivalent

attribute [instance] PresupposingFamily.boolDom

/-- A family of modal operators over worlds, indexed by what a construction leaves open. -/
structure ModalFamily where
  /-- What the construction leaves open. -/
  Param : Type 1
  /-- The worlds. -/
  W : Param → Type
  /-- The operator at each parameter. -/
  op : ∀ p, Set (W p) → Set (W p)

/-- A family of operators on a scale with stronger scale-mates. Each operator is paired with its
meaning enriched by its direct implicature, which is its exhaustification against those
scale-mates ([gajewski-2011]'s `O` with `ALT-1`). -/
structure ScalarFamily extends OperatorFamily where
  /-- The operator exhaustified against its stronger scale-mates, at each parameter. -/
  exhaustified : ∀ p, Dom p → Cod p

end Licenser

/-- The operator that a construction places over the position of a polarity item. It is
classical, scalar with its enrichment, a map into trivalent propositions, or modal. -/
inductive Licenser : Type 2 where
  | classical (F : Licenser.OperatorFamily)
  | scalar (F : Licenser.ScalarFamily)
  | strawson (F : Licenser.PresupposingFamily)
  | modal (F : Licenser.ModalFamily)

namespace Licenser

/-- The meaning of a licenser above the exhaustivity operator. A scalar licenser takes the meaning
of its enriched operators, and any other licenser keeps its own meaning. -/
def exhaustified : Licenser → Licenser
  | .scalar F => .classical { F.toOperatorFamily with op := F.exhaustified }
  | L => L

/-- A licenser *holds* a strength of negation outright when every operator in its family has it.
An operator into trivalent propositions holds the strength on its truth set, and a scalar operator
holds it on its plain meaning. -/
def Holds : Licenser → Negation.Strength → Prop
  | .classical F, s | .scalar ⟨F, _⟩, s => ∀ p, Negation.HasStrength (F.op p) s
  | .strawson F, s => ∀ p, Negation.HasStrength (fun x ↦ Trivalent.posExt (F.op p x)) s
  | .modal F, s => ∀ p, Negation.HasStrength (F.op p) s

/-- A licenser is Strawson downward entailing when every operator in its family is downward
entailing modulo its presupposition. -/
def IsStrawsonDE : Licenser → Prop
  | .classical F | .scalar ⟨F, _⟩ => ∀ p, Antitone (F.op p)
  | .strawson F => ∀ p, Presupposition.IsStrawsonDE (F.op p)
  | .modal F => ∀ p, Antitone (F.op p)

/-- A licenser is Strawson upward entailing when every operator in its family is upward entailing
modulo its presupposition. A constant operator is both upward and downward entailing. -/
def IsStrawsonUE : Licenser → Prop
  | .classical F | .scalar ⟨F, _⟩ => ∀ p, Monotone (F.op p)
  | .strawson F => ∀ p, Presupposition.IsStrawsonUE (F.op p)
  | .modal F => ∀ p, Monotone (F.op p)

/-- A licenser *carries* the monotone decreasing strength when it is downward entailing and not
upward entailing modulo presupposition. This is the condition that [von-fintel-1999],
[gajewski-2011]'s Condition 1, and [bylinina-nouwen-2018]'s (53) place on the meaning below the exhaustivity operator. A
licenser carries a stronger strength when, in addition, its exhaustified meaning holds that
strength outright. -/
def Carries (L : Licenser) : Negation.Strength → Prop
  | .monotoneDecreasing => L.IsStrawsonDE ∧ ¬ L.IsStrawsonUE
  | s => (L.IsStrawsonDE ∧ ¬ L.IsStrawsonUE) ∧ L.exhaustified.Holds s

section OfOperator

variable {σ P : Type} [BooleanAlgebra σ] [BooleanAlgebra P] {f : σ → P} {s : Negation.Strength}

/-- The classical licenser of a single operator over the position of a polarity item. -/
def ofOperator (f : σ → P) : Licenser :=
  .classical { Param := PUnit, Dom := fun _ ↦ σ, Cod := fun _ ↦ P, op := fun _ ↦ f }

/-- A single operator carries a strength of negation exactly when it has the strength and is not
upward entailing. -/
theorem carries_ofOperator_iff :
    (ofOperator f).Carries s ↔ Negation.HasStrength f s ∧ ¬Monotone f := by
  have ha (h : Negation.HasStrength f s) : Antitone f := h.of_le (s := .monotoneDecreasing) bot_le
  cases s <;>
    simp only [ofOperator, Carries, IsStrawsonDE, IsStrawsonUE, exhaustified, Holds]
  · exact ⟨fun h ↦ ⟨h.1 ⟨⟩, fun hm ↦ h.2 fun _ ↦ hm⟩, fun h ↦ ⟨fun _ ↦ h.1, fun hm ↦ h.2 (hm ⟨⟩)⟩⟩
  all_goals exact ⟨fun h ↦ ⟨h.2 ⟨⟩, fun hm ↦ h.1.2 fun _ ↦ hm⟩,
    fun h ↦ ⟨⟨fun _ ↦ ha h.1, fun hm ↦ h.2 (hm ⟨⟩)⟩, fun _ ↦ h.1⟩⟩

end OfOperator

/-- A licenser *licenses by strengthening* when widening the domain of an existential strengthens
the result under each of its operators. That is, the existential over the wider domain entails,
modulo presupposition, the existential over the narrower domain ([kadmon-landman-1993]). -/
def LicensesByStrengthening : Licenser → Prop
  | .classical F | .scalar ⟨F, _⟩ => ∀ p (E : Type) (P : E → F.Dom p) ⦃D D' : Finset E⦄,
      D ⊆ D' → F.op p (D'.sup P) ≤ F.op p (D.sup P)
  | .strawson F => ∀ p (E : Type) (P : E → F.Dom p) ⦃D D' : Finset E⦄,
      D ⊆ D' → strawsonEntails (F.op p (D'.sup P)) (F.op p (D.sup P))
  | .modal F => ∀ p (E : Type) (P : E → Set (F.W p)) ⦃D D' : Finset E⦄,
      D ⊆ D' → F.op p (D'.sup P) ≤ F.op p (D.sup P)

/-- A modal licenser *licenses free choice* when the antiexhaustified existential is consistent
under one of its operators, over a domain of at least two possible witnesses
([chierchia-2006]). -/
def LicensesFreeChoice : Licenser → Prop
  | .modal F => ∃ p, ∃ (E : Type) (P : E → Set (F.W p)) (D : Finset E), 1 < D.card ∧
      (antiExh (fun S ↦ F.op p (⋃ a ∈ S, P a)) D).Nonempty
  | .classical _ | .scalar _ | .strawson _ => False

variable {L : Licenser} {s t : Negation.Strength}

theorem Holds.of_le (h : L.Holds t) (hst : s ≤ t) : L.Holds s := by
  cases L with
  | classical F | strawson F | modal F => exact fun p ↦ (h p).of_le hst
  | scalar F => exact fun p ↦ (h p).of_le hst

theorem isStrawsonDE_of_holds_monotoneDecreasing (h : L.Holds .monotoneDecreasing) :
    L.IsStrawsonDE := by
  cases L with
  | classical F => exact fun p ↦ h p
  | scalar F => exact fun p ↦ h p
  | strawson F => exact fun p ↦ Presupposition.IsStrawsonDE.of_antitone_posExt (h p)
  | modal F => exact fun p ↦ h p

/-- Widening the domain strengthens under every operator of a licenser exactly when the licenser
is downward entailing modulo presupposition. -/
theorem licensesByStrengthening_iff : L.LicensesByStrengthening ↔ L.IsStrawsonDE := by
  classical
  rcases L with F | ⟨F, _⟩ | F | _
  all_goals exact ⟨fun h p a b hab ↦ by
          simpa [sup_eq_left.2 hab] using h p _ id (Finset.subset_insert b {a}),
        fun h p _ _ _ _ hD ↦ h p (Finset.sup_mono hD)⟩

theorem Carries.monotoneDecreasing (h : L.Carries s) : L.Carries .monotoneDecreasing := by
  cases s with
  | monotoneDecreasing => exact h
  | antiAdditive | antimorphic => exact h.1

theorem Carries.of_le (h : L.Carries s) (hts : t ≤ s) : L.Carries t := by
  cases t with
  | monotoneDecreasing => exact h.monotoneDecreasing
  | antiAdditive | antimorphic =>
    cases s with
    | monotoneDecreasing => exact absurd hts (by decide)
    | antiAdditive | antimorphic => exact ⟨h.1, h.2.of_le hts⟩

theorem carries_iff_of_ne_monotoneDecreasing (hs : s ≠ .monotoneDecreasing) :
    L.Carries s ↔ L.Carries .monotoneDecreasing ∧ L.exhaustified.Holds s := by
  cases s with
  | monotoneDecreasing => exact absurd rfl hs
  | antiAdditive | antimorphic => exact Iff.rfl

/-- A classical licenser carries a strength exactly when it holds that strength outright and is
non-trivial. -/
theorem carries_classical_iff {F : OperatorFamily} :
    (classical F).Carries s ↔ (classical F).Holds s ∧ ¬ (classical F).IsStrawsonUE := by
  cases s with
  | monotoneDecreasing => exact Iff.rfl
  | antiAdditive | antimorphic =>
    exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦
      ⟨⟨isStrawsonDE_of_holds_monotoneDecreasing (h.1.of_le (by decide)), h.2⟩, h.1⟩⟩

/-- A non-trivial classical licenser that holds exactly the strengths up to `s₀` carries exactly
those strengths. -/
theorem carries_classical_iff_le {F : OperatorFamily} {s₀ : Negation.Strength}
    (hn : ¬ (classical F).IsStrawsonUE)
    (h : ∀ s, (classical F).Holds s ↔ s ≤ s₀) :
    (classical F).Carries s ↔ s ≤ s₀ := by
  rw [carries_classical_iff, h, and_iff_left hn]

/-- A non-trivial licenser that is downward entailing modulo presupposition and holds exactly the
strengths up to `s₀` once exhaustified carries exactly those strengths. -/
theorem carries_iff_le {s₀ : Negation.Strength} (hde : L.IsStrawsonDE) (hn : ¬ L.IsStrawsonUE)
    (h : ∀ s, L.exhaustified.Holds s ↔ s ≤ s₀) : L.Carries s ↔ s ≤ s₀ := by
  cases s with
  | monotoneDecreasing => exact iff_of_true ⟨hde, hn⟩ (Negation.Strength.monotoneDecreasing_le _)
  | antiAdditive | antimorphic => exact (and_iff_right ⟨hde, hn⟩).trans (h _)

/-- A presupposing licenser carries anti-additive strength when its truth sets are anti-additive
and one of its operators is not upward entailing. -/
theorem carries_strawson_antiAdditive {F : PresupposingFamily}
    (h : ∀ p, Negation.HasStrength (fun x ↦ Trivalent.posExt (F.op p x)) .antiAdditive)
    (hn : ∃ p, ¬ Presupposition.IsStrawsonUE (F.op p)) : (strawson F).Carries .antiAdditive :=
  have hh : (strawson F).Holds .antiAdditive := fun p ↦ h p
  ⟨⟨isStrawsonDE_of_holds_monotoneDecreasing (hh.of_le (by decide)),
    fun hu ↦ hn.elim fun p hp ↦ hp (hu p)⟩, hh⟩

theorem not_carries_strawson_antiAdditive {F : PresupposingFamily}
    (h : ∃ p, ¬ Negation.HasStrength (fun x ↦ Trivalent.posExt (F.op p x)) .antiAdditive) :
    ¬ (strawson F).Carries .antiAdditive :=
  fun hc ↦ h.elim fun p hp ↦ hp (hc.2 p)

/-- A licenser that holds a strength and none above it holds exactly the strengths up to it. -/
theorem holds_iff_le {s₀ : Negation.Strength} (h : L.Holds s₀)
    (hn : ∀ s, s₀ < s → ¬ L.Holds s) : L.Holds s ↔ s ≤ s₀ :=
  ⟨fun hs ↦ not_lt.mp fun hlt ↦ hn s hlt hs, fun hs ↦ h.of_le hs⟩

theorem not_holds_of_not_holds_monotoneDecreasing (h : ¬ L.Holds .monotoneDecreasing) :
    ¬ L.Holds s :=
  fun hs ↦ h (hs.of_le bot_le)

/-- A non-trivial licenser that is downward entailing modulo presupposition, but not downward
entailing outright once its direct implicature is added, carries exactly the monotone decreasing
strength ([gajewski-2011]). -/
theorem carries_iff_eq_monotoneDecreasing (hde : L.IsStrawsonDE) (hn : ¬ L.IsStrawsonUE)
    (h : ¬ L.exhaustified.Holds .monotoneDecreasing) : L.Carries s ↔ s = .monotoneDecreasing := by
  cases s with
  | monotoneDecreasing => exact iff_of_true ⟨hde, hn⟩ rfl
  | antiAdditive | antimorphic =>
    exact iff_of_false (fun hc ↦ not_holds_of_not_holds_monotoneDecreasing h hc.2) (by decide)

/-! ### The strengths a licenser carries and holds

The strengths that a licenser carries form a lower set of the chain of strengths, and so do the
strengths that it holds outright. Each set is therefore determined by its greatest element, taken
in the chain extended by a least element that stands for no strength. -/

open scoped Classical in
/-- The greatest strength of negation that a licenser carries, or `⊥` if it carries none. -/
noncomputable def carried (L : Licenser) : WithBot Negation.Strength :=
  (Finset.univ.filter L.Carries).sup (↑)

open scoped Classical in
/-- The greatest strength of negation that a licenser holds outright, or `⊥` if it holds none. -/
noncomputable def held (L : Licenser) : WithBot Negation.Strength :=
  (Finset.univ.filter fun s : Negation.Strength ↦ L.Holds s).sup (↑)

private theorem coe_le_sup_filter_iff {P : Negation.Strength → Prop} [DecidablePred P]
    (hP : ∀ ⦃s t : Negation.Strength⦄, P s → t ≤ s → P t) :
    (s : WithBot Negation.Strength) ≤ (Finset.univ.filter P).sup (↑) ↔ P s := by
  rw [Finset.le_sup_iff (WithBot.bot_lt_coe _)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, WithBot.coe_le_coe]
  exact ⟨fun ⟨_, ht, hst⟩ ↦ hP ht hst, fun h ↦ ⟨s, h, le_rfl⟩⟩

theorem coe_le_carried_iff : (s : WithBot Negation.Strength) ≤ L.carried ↔ L.Carries s := by
  classical
  unfold carried
  exact coe_le_sup_filter_iff fun _ _ h hts ↦ h.of_le hts

theorem coe_le_held_iff : (s : WithBot Negation.Strength) ≤ L.held ↔ L.Holds s := by
  classical
  unfold held
  exact coe_le_sup_filter_iff fun _ _ h hts ↦ h.of_le hts

/-- A non-trivial classical licenser carries exactly the strengths that it holds. -/
theorem carried_classical {F : OperatorFamily} (hn : ¬ (classical F).IsStrawsonUE) :
    (classical F).carried = (classical F).held := by
  classical
  simp only [carried, held, carries_classical_iff, and_iff_left hn]

end Licenser

/-! ### Licensing -/

namespace Licenser

variable {L : Licenser} {s s₀ : Negation.Strength}

/-- A licenser that carries exactly the strengths up to `s₀` carries `s₀` as its greatest. -/
theorem carried_eq_coe (h : ∀ s, L.Carries s ↔ s ≤ s₀) : L.carried = s₀ := by
  refine le_antisymm ?_ (coe_le_carried_iff.2 ((h s₀).2 le_rfl))
  cases ht : L.carried with
  | bot => exact bot_le
  | coe t => exact WithBot.coe_le_coe.2 ((h t).1 (coe_le_carried_iff.1 ht.ge))

theorem carried_eq_bot (h : ∀ s, ¬ L.Carries s) : L.carried = ⊥ := by
  cases ht : L.carried with
  | bot => rfl
  | coe t => exact absurd (coe_le_carried_iff.1 ht.ge) (h t)

/-- A licenser that holds exactly the strengths up to `s₀` holds `s₀` as its greatest. -/
theorem held_eq_coe (h : ∀ s, L.Holds s ↔ s ≤ s₀) : L.held = s₀ := by
  refine le_antisymm ?_ (coe_le_held_iff.2 ((h s₀).2 le_rfl))
  cases ht : L.held with
  | bot => exact bot_le
  | coe t => exact WithBot.coe_le_coe.2 ((h t).1 (coe_le_held_iff.1 ht.ge))

theorem held_eq_bot (h : ∀ s : Negation.Strength, ¬ L.Holds s) : L.held = ⊥ := by
  cases ht : L.held with
  | bot => rfl
  | coe t => exact absurd (coe_le_held_iff.1 ht.ge) (h t)

variable (L) (d : Distribution)

/-- The negativity of a licenser: the greatest strength it carries and the greatest it holds. -/
noncomputable def negativity : Negativity := ⟨L.carried, L.held⟩

@[simp] theorem negativity_carried : L.negativity.carried = L.carried := rfl

@[simp] theorem negativity_held : L.negativity.held = L.held := rfl

open scoped Classical in
/-- A licenser **admits** a distribution when the context it makes lies in the distribution. -/
def Admits : Prop := (L.negativity, decide L.LicensesFreeChoice) ∈ d

variable {L d} {d' : Distribution} {F : OperatorFamily}

theorem Admits.mono (h : L.Admits d) (hd : d ≤ d') : L.Admits d' := IsConcreteLE.le_iff.1 hd h

@[simp] theorem admits_sup : L.Admits (d ⊔ d') ↔ L.Admits d ∨ L.Admits d' := by
  simp [Admits]

@[simp] theorem admits_inf : L.Admits (d ⊓ d') ↔ L.Admits d ∧ L.Admits d' := by
  simp [Admits]

/-- The negative polarity items of a strength are admitted exactly by the licensers that carry
it. -/
@[simp] theorem admits_npi_iff : L.Admits (.npi s) ↔ L.Carries s := by
  simp [Admits, coe_le_carried_iff]

/-- The positive polarity items of a strength are admitted exactly by the licensers that do not
hold it. -/
@[simp] theorem admits_ppi_iff : L.Admits (.ppi s) ↔ ¬ L.Holds s := by
  simp [Admits, coe_le_held_iff]

/-- The free choice items are admitted exactly by the licensers that license free choice. -/
@[simp] theorem admits_fci_iff : L.Admits .fci ↔ L.LicensesFreeChoice := by
  simp [Admits]

/-- A non-trivial classical context admits the positive polarity items of a strength exactly where
it does not admit the negative polarity items of that strength. This is the mirror image of
[vanderwouden-1997]'s table of distributions. -/
theorem admits_ppi_iff_not_admits_npi (hn : ¬ (classical F).IsStrawsonUE) :
    (classical F).Admits (.ppi s) ↔ ¬ (classical F).Admits (.npi s) := by
  simp [carries_classical_iff, hn]

end Licenser

end PolarityItem
