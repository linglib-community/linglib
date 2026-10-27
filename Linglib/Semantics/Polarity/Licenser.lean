/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Soundness
public import Linglib.Logic.Natural.Strawson
public import Linglib.Semantics.Exhaustification.Antiexhaustive
public import Linglib.Semantics.Questions.Value
public import Linglib.Semantics.Polarity.Strength

/-!
# Licensers

A *licenser* is the operator a construction places over the position of a polarity item, given
as a family of operators indexed by what the construction leaves open (the model, a restrictor, a
bound or an accessibility relation). It is classical (a map between bounded lattices), scalar (one
with stronger scale-mates), Strawsonian (von Fintel's map into trivalent propositions), modal, or
a wh-question. A licenser has a plain meaning below the exhaustivity operator and, after
Gajewski, a meaning above it that adds its direct implicature, the exhaustification against its
stronger scale-mates; only a scalar licenser has a direct implicature.

## Main definitions

* `PolarityItem.Licenser`: the five kinds of licenser.
* `PolarityItem.Licenser.exhaustified`: the licenser with its direct implicature factored in.
* `PolarityItem.Licenser.Holds`, `PolarityItem.Licenser.IsStrawsonDE`,
  `PolarityItem.Licenser.IsStrawsonUE`: a signature held outright, and downward and upward
  entailment modulo presupposition.
* `PolarityItem.Licenser.Carries`: a strength of negation carried. Every negative polarity item
  needs the plain meaning downward entailing modulo presupposition (von Fintel) and not upward
  entailing as well (Bylinina and Nouwen); a stronger strength must hold outright of the
  exhaustified meaning.
* `PolarityItem.Licenser.LicensesFreeChoice`, `PolarityItem.Licenser.LicensesByRelevance`: the
  free-choice route of a modal licenser (Chierchia) and the relevance route of a question
  (van Rooy).

## Implementation notes

* Gajewski asks only for downward entailment of the exhaustified meaning; Zwarts's strengths are
  kept here, and agree with Gajewski's condition at the endpoints of the scale.
* The unit conditions of `Signature.HoldsFor` do not exclude constant maps, which are downward
  entailing and, if constantly false, anti-additive; requiring weak strength not to be upward
  entailing as well excludes them.
* The question route states the weak form the theory of question value proves, that widening
  never lowers the question's value; van Rooy's strict condition for rhetorical questions is not
  formalized.

## References

* [von-fintel-1999]
* [gajewski-2011]
* [zwarts-1998]
* [bylinina-nouwen-2018]
* [icard-2012]
* [chierchia-2006]
* [van-rooy-2003-npi]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic Presupposition Exhaustification MeasureTheory

/-- A family of operators between bounded lattices, indexed by what a construction leaves open. -/
structure OperatorFamily where
  /-- What the construction leaves open. -/
  Param : Type 1
  /-- The lattice the item's position ranges over. -/
  Dom : Param → Type
  /-- The lattice of the result. -/
  Cod : Param → Type
  /-- The domain is a lattice. -/
  [latDom : ∀ p, Lattice (Dom p)]
  /-- The domain is bounded. -/
  [bndDom : ∀ p, BoundedOrder (Dom p)]
  /-- The codomain is a lattice. -/
  [latCod : ∀ p, Lattice (Cod p)]
  /-- The codomain is bounded. -/
  [bndCod : ∀ p, BoundedOrder (Cod p)]
  /-- The operator at each parameter. -/
  op : ∀ p, Dom p → Cod p

attribute [instance] OperatorFamily.latDom OperatorFamily.bndDom OperatorFamily.latCod
  OperatorFamily.bndCod

/-- A family of operators into trivalent propositions, indexed by what a construction leaves
open. -/
structure PresupposingFamily where
  /-- What the construction leaves open. -/
  Param : Type 1
  /-- The lattice the item's position ranges over. -/
  Dom : Param → Type
  /-- The worlds of the trivalent propositions. -/
  W : Param → Type
  /-- The domain is a lattice. -/
  [latDom : ∀ p, Lattice (Dom p)]
  /-- The domain is bounded. -/
  [bndDom : ∀ p, BoundedOrder (Dom p)]
  /-- The operator at each parameter. -/
  op : ∀ p, Dom p → W p → SignType

attribute [instance] PresupposingFamily.latDom PresupposingFamily.bndDom

/-- A family of modal operators over worlds, indexed by what a construction leaves open. -/
structure ModalFamily where
  /-- What the construction leaves open. -/
  Param : Type 1
  /-- The worlds. -/
  W : Param → Type
  /-- The operator at each parameter. -/
  op : ∀ p, Set (W p) → Set (W p)

/-- A family of operators on a scale with stronger mates, each paired with its meaning enriched
by its direct implicature, the exhaustification against those mates ([gajewski-2011]'s `O` with
`ALT-1`). -/
structure ScalarFamily extends OperatorFamily where
  /-- The operator exhaustified against its stronger scale-mates, at each parameter. -/
  exhaustified : ∀ p, Dom p → Cod p

/-- The operator that a construction places over the position of a polarity item is classical,
scalar (with its enrichment), into trivalent propositions, modal, or a question. -/
inductive Licenser : Type 2 where
  | classical (F : OperatorFamily)
  | scalar (F : ScalarFamily)
  | strawson (F : PresupposingFamily)
  | modal (F : ModalFamily)
  | question

/-- A context licenses polarity items by strengthening, as a generic context licensing free choice
items ([kadmon-landman-1993], [dayal-1996]), or by the relevance of a question
([van-rooy-2003-npi]). -/
inductive LicensingMechanism where
  | strengthening
  | genericIndefinite
  | entropy
  deriving DecidableEq, Repr

namespace Licenser

/-- Above the exhaustivity operator, a scalar licenser has the meaning of its enriched operators,
and any other licenser keeps its own meaning. -/
def exhaustified : Licenser → Licenser
  | .scalar F => .classical { F.toOperatorFamily with op := F.exhaustified }
  | L => L

/-- A licenser holds a signature outright when every operator in its family does; an operator into
trivalent propositions holds it on its truth set, and a scalar operator on its plain meaning. -/
def Holds : Licenser → Signature → Prop
  | .classical F, σ | .scalar ⟨F, _⟩, σ => ∀ p, σ.HoldsFor (F.op p)
  | .strawson F, σ => ∀ p, σ.HoldsFor fun x ↦ posSupport (F.op p x)
  | .modal _, _ | .question, _ => False

/-- A licenser is Strawson downward entailing when every operator in its family is downward
entailing modulo its presupposition. -/
def IsStrawsonDE : Licenser → Prop
  | .classical F | .scalar ⟨F, _⟩ => ∀ p, Antitone (F.op p)
  | .strawson F => ∀ p, NaturalLogic.IsStrawsonDE (F.op p)
  | .modal _ | .question => False

/-- A licenser is Strawson upward entailing when every operator in its family is upward entailing
modulo its presupposition; a constant operator is both this and downward entailing. -/
def IsStrawsonUE : Licenser → Prop
  | .classical F | .scalar ⟨F, _⟩ => ∀ p, Monotone (F.op p)
  | .strawson F => ∀ p, NaturalLogic.IsStrawsonUE (F.op p)
  | .modal _ | .question => False

/-- A licenser carries weak strength when it is downward and not upward entailing modulo
presupposition. This is the condition every negative polarity item puts on the meaning below the
exhaustivity operator ([von-fintel-1999], [gajewski-2011]'s Condition 1,
[bylinina-nouwen-2018]'s (53)). It carries a stronger strength when, in addition, its exhaustified
meaning holds that strength outright. -/
def Carries (L : Licenser) : Negation.Strength → Prop
  | .weak => L.IsStrawsonDE ∧ ¬ L.IsStrawsonUE
  | s => (L.IsStrawsonDE ∧ ¬ L.IsStrawsonUE) ∧ L.exhaustified.Holds s.toSignature

/-- The route by which a licenser licenses. -/
def mechanism : Licenser → LicensingMechanism
  | .classical _ | .scalar _ | .strawson _ => .strengthening
  | .modal _ => .genericIndefinite
  | .question => .entropy

/-- A modal licenser licenses free choice when, under one of its operators and over a domain of at
least two possible witnesses, the antiexhaustified existential is consistent
([chierchia-2006]). -/
def LicensesFreeChoice : Licenser → Prop
  | .modal F => ∃ p, ∃ (E : Type) (P : E → Set (F.W p)) (D : Finset E), 1 < D.card ∧
      (oMinus (fun S ↦ F.op p (⋃ a ∈ S, P a)) D).Nonempty
  | .classical _ | .scalar _ | .strawson _ | .question => False

/-- A question licenses a domain widener by relevance, since widening the domain of a wh-question
never lowers its value in any decision problem ([van-rooy-2003-npi]). -/
def LicensesByRelevance : Licenser → Prop
  | .question => ∀ {W A D : Type} [Fintype W] [DecidableEq W] [DecidableEq D] [MeasurableSpace W]
      [DiscreteMeasurableSpace W] [Finite A] [Nonempty W] (U : W → A → ℝ) (μ : Measure W)
      [IsProbabilityMeasure μ] (P : W → Finset D) (dom dom' : Finset D), dom ⊆ dom' →
      Question.utility U μ (Question.wh P dom) ≤ Question.utility U μ (Question.wh P dom')
  | .classical _ | .scalar _ | .strawson _ | .modal _ => False

theorem licensesByRelevance_question : question.LicensesByRelevance :=
  fun U μ _ P _ _ h ↦ Question.utility_wh_mono U μ P h

variable {L : Licenser} {σ τ : Signature} {s t : Negation.Strength}

theorem Holds.of_le (h : L.Holds σ) (hστ : σ ≤ τ) : L.Holds τ := by
  cases L with
  | classical F | strawson F => exact fun p ↦ (h p).of_le hστ
  | scalar F => exact fun p ↦ (h p).of_le hστ
  | modal _ | question => exact h

theorem Holds.toSignature_of_le (h : L.Holds t.toSignature) (hst : s ≤ t) :
    L.Holds s.toSignature :=
  h.of_le (Negation.Strength.toSignature_antitone hst)

theorem isStrawsonDE_of_holds_anti (h : L.Holds .anti) : L.IsStrawsonDE := by
  cases L with
  | classical F => exact fun p ↦ Signature.holdsFor_anti_iff.mp (h p)
  | scalar F => exact fun p ↦ Signature.holdsFor_anti_iff.mp (h p)
  | strawson F =>
    exact fun p ↦ NaturalLogic.IsStrawsonDE.of_antitone_posSupport
      (Signature.holdsFor_anti_iff.mp (h p))
  | modal _ | question => exact h

theorem Carries.weak (h : L.Carries s) : L.Carries .weak := by
  cases s with
  | weak => exact h
  | antiAdditive | antiMorphic => exact h.1

theorem Carries.of_le (h : L.Carries s) (hts : t ≤ s) : L.Carries t := by
  cases t with
  | weak => exact h.weak
  | antiAdditive | antiMorphic =>
    cases s with
    | weak => exact absurd hts (by decide)
    | antiAdditive | antiMorphic => exact ⟨h.1, h.2.toSignature_of_le hts⟩

theorem carries_iff_of_ne_weak (hs : s ≠ .weak) :
    L.Carries s ↔ L.Carries .weak ∧ L.exhaustified.Holds s.toSignature := by
  cases s with
  | weak => exact absurd rfl hs
  | antiAdditive | antiMorphic => exact Iff.rfl

/-- A classical licenser carries a strength exactly when it holds it outright and is
non-trivial. -/
theorem carries_classical_iff {F : OperatorFamily} :
    (classical F).Carries s ↔ (classical F).Holds s.toSignature ∧ ¬ (classical F).IsStrawsonUE := by
  cases s with
  | weak => exact and_congr_left' (forall_congr' fun _ ↦ Signature.holdsFor_anti_iff.symm)
  | antiAdditive | antiMorphic =>
    exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦
      ⟨⟨isStrawsonDE_of_holds_anti (h.1.toSignature_of_le (s := .weak) (by decide)), h.2⟩, h.1⟩⟩

theorem holds_toSignature_iff {s₀ : Negation.Strength} (h : L.Holds s₀.toSignature)
    (hn : ∀ s, s₀ < s → ¬ L.Holds s.toSignature) : L.Holds s.toSignature ↔ s ≤ s₀ :=
  ⟨fun hs ↦ not_lt.mp fun hlt ↦ hn s hlt hs, fun hs ↦ h.toSignature_of_le hs⟩

theorem not_holds_toSignature (h : ¬ L.Holds .anti) : ¬ L.Holds s.toSignature := fun hs ↦
  h (hs.of_le (Negation.Strength.toSignature_antitone
    (by cases s <;> decide : Negation.Strength.weak ≤ s)))

/-- A non-trivial licenser that is downward entailing modulo presupposition, and not outright once
its direct implicature is factored in, carries exactly weak strength ([gajewski-2011]). -/
theorem carries_iff_eq_weak (hde : L.IsStrawsonDE) (hn : ¬ L.IsStrawsonUE)
    (h : ¬ L.exhaustified.Holds .anti) : L.Carries s ↔ s = .weak := by
  cases s with
  | weak => exact iff_of_true ⟨hde, hn⟩ rfl
  | antiAdditive | antiMorphic =>
    exact iff_of_false (fun hc ↦ not_holds_toSignature h hc.2) (by decide)

end Licenser

end PolarityItem
