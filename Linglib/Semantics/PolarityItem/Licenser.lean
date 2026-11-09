/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.ProjectivitySignature
public import Linglib.Semantics.Presupposition.Strawson
public import Linglib.Semantics.Exhaustification.Antiexhaustive
public import Linglib.Semantics.Questions.Value
public import Linglib.Semantics.PolarityItem.Basic

/-!
# Licensers

A *licenser* is the operator a construction places over the position of a polarity item, given
as a family of operators indexed by what the construction leaves open (the model, a restrictor, a
bound or an accessibility relation). It is classical (a map between bounded lattices), scalar (one
with stronger scale-mates), Strawsonian (von Fintel's map into trivalent propositions), modal, or
a wh-question. A licenser has a plain meaning below the exhaustivity operator and, after
Gajewski, a meaning above it that adds its direct implicature, the exhaustification against its
stronger scale-mates; only a scalar licenser has a direct implicature.

A context *licenses* a `PolarityItem` when the licenser it places over the item carries the
strength the item needs, licenses free choice and the item is a free choice item, or is a question
and the item a weak negative polarity item; it *anti-licenses* an item when its licenser holds the
blocking strength outright. A non-trivial classical context [admits an item exactly when its
strength lies in the item's interval](##PolarityItem.Licenser.admits_iff_carried_mem_Ico); it
[blocks the positive polarity items of a strength exactly where it licenses the negative
ones](##PolarityItem.Licenser.antiLicenses_iff_licenses), and an antimorphic context [blocks them
all](##PolarityItem.Licenser.antiLicenses_iff_isPPI).

## Main definitions

* `PolarityItem.Licenser`: the five kinds of licenser.
* `PolarityItem.Licenser.exhaustified`: the licenser with its direct implicature factored in.
* `PolarityItem.Licenser.Holds`, `PolarityItem.Licenser.IsStrawsonDE`,
  `PolarityItem.Licenser.IsStrawsonUE`: a signature held outright, and downward and upward
  entailment modulo presupposition.
* `PolarityItem.Licenser.Carries`: a strength of negation carried. Von Fintel asks the plain meaning
  to be downward entailing modulo presupposition, Bylinina and Nouwen add that it not be upward
  entailing as well, and a stronger strength must hold outright of the exhaustified meaning.
* `PolarityItem.Licenser.LicensesByStrengthening`, `PolarityItem.Licenser.LicensesFreeChoice`,
  `PolarityItem.Licenser.LicensesByRelevance`: the strengthening route of a downward-entailing
  licenser (Kadmon and Landman), the free-choice route of a modal licenser (Chierchia) and the
  relevance route of a question (van Rooy).
* `PolarityItem.Licenser.Licenses`, `PolarityItem.Licenser.AntiLicenses`,
  `PolarityItem.Licenser.Admits`: the licensing relation between a licenser and an item.

## Main statements

* `PolarityItem.Licenser.licensesByStrengthening_iff`: widening strengthens under a licenser
  exactly when the licenser is downward entailing modulo presupposition.

## Implementation notes

* Licensing reads the meaning modulo presupposition and with its direct implicature, after von
  Fintel and Gajewski; anti-licensing reads the plain meaning, as van der Wouden and Szabolcsi state
  it, for whom presuppositional operators such as *only* and *regret* rescue a positive polarity
  item rather than block it.
* Gajewski asks only for downward entailment of the exhaustified meaning; Zwarts's strengths are
  kept here, and agree with Gajewski's condition at the endpoints of the scale.
* The unit conditions of `ProjectivitySignature.HoldsFor` do not exclude constant maps, which are
  downward entailing and, if constantly false, anti-additive; requiring weak strength not to be
  upward entailing as well excludes them, since a map monotone both ways modulo presupposition
  takes one value at comparable arguments where defined
  (`Presupposition.isStrawsonUE_and_isStrawsonDE_iff`).
* The question route states the weak form the theory of question value proves, that widening
  never lowers the question's value; van Rooy's strict condition for rhetorical questions is not
  formalized.

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
* [van-rooy-2003-npi]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic Presupposition Exhaustification MeasureTheory

namespace Licenser

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
  op : ∀ p, Dom p → W p → Trivalent

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

end Licenser

/-- The operator that a construction places over the position of a polarity item is classical,
scalar (with its enrichment), into trivalent propositions, modal, or a question. -/
inductive Licenser : Type 2 where
  | classical (F : Licenser.OperatorFamily)
  | scalar (F : Licenser.ScalarFamily)
  | strawson (F : Licenser.PresupposingFamily)
  | modal (F : Licenser.ModalFamily)
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
def Holds : Licenser → ProjectivitySignature → Prop
  | .classical F, σ | .scalar ⟨F, _⟩, σ => ∀ p, σ.HoldsFor (F.op p)
  | .strawson F, σ => ∀ p, σ.HoldsFor fun x ↦ Trivalent.posExt (F.op p x)
  | .modal F, σ => ∀ p, σ.HoldsFor (F.op p)
  | .question, _ => False

/-- A licenser is Strawson downward entailing when every operator in its family is downward
entailing modulo its presupposition. -/
def IsStrawsonDE : Licenser → Prop
  | .classical F | .scalar ⟨F, _⟩ => ∀ p, Antitone (F.op p)
  | .strawson F => ∀ p, Presupposition.IsStrawsonDE (F.op p)
  | .modal F => ∀ p, Antitone (F.op p)
  | .question => False

/-- A licenser is Strawson upward entailing when every operator in its family is upward entailing
modulo its presupposition; a constant operator is both this and downward entailing. -/
def IsStrawsonUE : Licenser → Prop
  | .classical F | .scalar ⟨F, _⟩ => ∀ p, Monotone (F.op p)
  | .strawson F => ∀ p, Presupposition.IsStrawsonUE (F.op p)
  | .modal F => ∀ p, Monotone (F.op p)
  | .question => False

/-- A licenser carries weak strength when it is downward and not upward entailing modulo
presupposition, the condition [von-fintel-1999], [gajewski-2011]'s Condition 1 and
[bylinina-nouwen-2018]'s (53) put on the meaning below the exhaustivity operator. It carries a
stronger strength when, in addition, its exhaustified meaning holds that strength outright. -/
def Carries (L : Licenser) : Negation.Strength → Prop
  | .weak => L.IsStrawsonDE ∧ ¬ L.IsStrawsonUE
  | s => (L.IsStrawsonDE ∧ ¬ L.IsStrawsonUE) ∧ L.exhaustified.Holds s.toProjectivitySignature

section OfOperator

variable {σ P : Type} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] {f : σ → P}
  {s : Negation.Strength}

/-- The classical licenser of a single operator over the position of a polarity item. -/
def ofOperator (f : σ → P) : Licenser :=
  .classical { Param := PUnit, Dom := fun _ ↦ σ, Cod := fun _ ↦ P, op := fun _ ↦ f }

/-- A single operator carries a strength of negation when it is in the function class of the
strength and is not upward entailing. -/
theorem carries_ofOperator_iff :
    (ofOperator f).Carries s ↔ s.toProjectivitySignature.HoldsFor f ∧ ¬Monotone f := by
  have ha (h : s.toProjectivitySignature.HoldsFor f) : Antitone f :=
    ProjectivitySignature.holdsFor_anti_iff.1
      (h.of_le (Negation.Strength.toProjectivitySignature_antitone bot_le))
  cases s <;>
    simp only [ofOperator, Carries, IsStrawsonDE, IsStrawsonUE, exhaustified, Holds]
  · exact ⟨fun h ↦ ⟨ProjectivitySignature.holdsFor_anti_iff.2 (h.1 ⟨⟩), fun hm ↦ h.2 fun _ ↦ hm⟩,
      fun h ↦ ⟨fun _ ↦ ProjectivitySignature.holdsFor_anti_iff.1 h.1, fun hm ↦ h.2 (hm ⟨⟩)⟩⟩
  all_goals exact ⟨fun h ↦ ⟨h.2 ⟨⟩, fun hm ↦ h.1.2 fun _ ↦ hm⟩,
    fun h ↦ ⟨⟨fun _ ↦ ha h.1, fun hm ↦ h.2 (hm ⟨⟩)⟩, fun _ ↦ h.1⟩⟩

end OfOperator

/-- The route by which a licenser licenses. -/
def mechanism : Licenser → LicensingMechanism
  | .classical _ | .scalar _ | .strawson _ => .strengthening
  | .modal _ => .genericIndefinite
  | .question => .entropy

/-- A licenser licenses by strengthening when, under each of its operators, widening the domain of
an existential strengthens the result: the existential over the wider domain entails, modulo
presupposition, the existential over the narrower one ([kadmon-landman-1993]). -/
def LicensesByStrengthening : Licenser → Prop
  | .classical F | .scalar ⟨F, _⟩ => ∀ p (E : Type) (P : E → F.Dom p) ⦃D D' : Finset E⦄,
      D ⊆ D' → F.op p (D'.sup P) ≤ F.op p (D.sup P)
  | .strawson F => ∀ p (E : Type) (P : E → F.Dom p) ⦃D D' : Finset E⦄,
      D ⊆ D' → strawsonEntails (F.op p (D'.sup P)) (F.op p (D.sup P))
  | .modal F => ∀ p (E : Type) (P : E → Set (F.W p)) ⦃D D' : Finset E⦄,
      D ⊆ D' → F.op p (D'.sup P) ≤ F.op p (D.sup P)
  | .question => False

/-- A modal licenser licenses free choice when, under one of its operators and over a domain of at
least two possible witnesses, the antiexhaustified existential is consistent
([chierchia-2006]). -/
def LicensesFreeChoice : Licenser → Prop
  | .modal F => ∃ p, ∃ (E : Type) (P : E → Set (F.W p)) (D : Finset E), 1 < D.card ∧
      (antiExh (fun S ↦ F.op p (⋃ a ∈ S, P a)) D).Nonempty
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

variable {L : Licenser} {σ τ : ProjectivitySignature} {s t : Negation.Strength}

theorem Holds.of_le (h : L.Holds σ) (hστ : σ ≤ τ) : L.Holds τ := by
  cases L with
  | classical F | strawson F | modal F => exact fun p ↦ (h p).of_le hστ
  | scalar F => exact fun p ↦ (h p).of_le hστ
  | question => exact h

theorem Holds.toProjectivitySignature_of_le (h : L.Holds t.toProjectivitySignature) (hst : s ≤ t) :
    L.Holds s.toProjectivitySignature :=
  h.of_le (Negation.Strength.toProjectivitySignature_antitone hst)

theorem isStrawsonDE_of_holds_anti (h : L.Holds .anti) : L.IsStrawsonDE := by
  cases L with
  | classical F => exact fun p ↦ ProjectivitySignature.holdsFor_anti_iff.mp (h p)
  | scalar F => exact fun p ↦ ProjectivitySignature.holdsFor_anti_iff.mp (h p)
  | strawson F =>
    exact fun p ↦ Presupposition.IsStrawsonDE.of_antitone_posExt
      (ProjectivitySignature.holdsFor_anti_iff.mp (h p))
  | modal F => exact fun p ↦ ProjectivitySignature.holdsFor_anti_iff.mp (h p)
  | question => exact h

/-- Widening strengthens under every operator of a licenser exactly when the licenser is downward
entailing modulo presupposition. -/
theorem licensesByStrengthening_iff : L.LicensesByStrengthening ↔ L.IsStrawsonDE := by
  classical
  rcases L with F | ⟨F, _⟩ | F | _ | _
  all_goals first
    | exact Iff.rfl
    | exact ⟨fun h p a b hab ↦ by
          simpa [sup_eq_left.2 hab] using h p _ id (Finset.subset_insert b {a}),
        fun h p _ _ _ _ hD ↦ h p (Finset.sup_mono hD)⟩

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
    | antiAdditive | antiMorphic => exact ⟨h.1, h.2.toProjectivitySignature_of_le hts⟩

theorem carries_iff_of_ne_weak (hs : s ≠ .weak) :
    L.Carries s ↔ L.Carries .weak ∧ L.exhaustified.Holds s.toProjectivitySignature := by
  cases s with
  | weak => exact absurd rfl hs
  | antiAdditive | antiMorphic => exact Iff.rfl

/-- A classical licenser carries a strength exactly when it holds it outright and is
non-trivial. -/
theorem carries_classical_iff {F : OperatorFamily} :
    (classical F).Carries s ↔
      (classical F).Holds s.toProjectivitySignature ∧ ¬ (classical F).IsStrawsonUE := by
  cases s with
  | weak => exact and_congr_left' (forall_congr' fun _ ↦
    ProjectivitySignature.holdsFor_anti_iff.symm)
  | antiAdditive | antiMorphic =>
    exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦
      ⟨⟨isStrawsonDE_of_holds_anti (h.1.toProjectivitySignature_of_le (s := .weak) (by decide)),
        h.2⟩, h.1⟩⟩

/-- A non-trivial classical licenser holding exactly the strengths up to `s₀` carries exactly
those. -/
theorem carries_classical_iff_le {F : OperatorFamily} {s₀ : Negation.Strength}
    (hn : ¬ (classical F).IsStrawsonUE)
    (h : ∀ s, (classical F).Holds s.toProjectivitySignature ↔ s ≤ s₀) :
    (classical F).Carries s ↔ s ≤ s₀ := by
  rw [carries_classical_iff, h, and_iff_left hn]

theorem holds_toProjectivitySignature_iff {s₀ : Negation.Strength}
    (h : L.Holds s₀.toProjectivitySignature)
    (hn : ∀ s, s₀ < s → ¬ L.Holds s.toProjectivitySignature) :
    L.Holds s.toProjectivitySignature ↔ s ≤ s₀ :=
  ⟨fun hs ↦ not_lt.mp fun hlt ↦ hn s hlt hs, fun hs ↦ h.toProjectivitySignature_of_le hs⟩

theorem not_holds_toProjectivitySignature (h : ¬ L.Holds .anti) :
    ¬ L.Holds s.toProjectivitySignature := fun hs ↦
  h (hs.of_le (Negation.Strength.toProjectivitySignature_antitone bot_le))

/-- A non-trivial licenser that is downward entailing modulo presupposition, and not outright once
its direct implicature is factored in, carries exactly weak strength ([gajewski-2011]). -/
theorem carries_iff_eq_weak (hde : L.IsStrawsonDE) (hn : ¬ L.IsStrawsonUE)
    (h : ¬ L.exhaustified.Holds .anti) : L.Carries s ↔ s = .weak := by
  cases s with
  | weak => exact iff_of_true ⟨hde, hn⟩ rfl
  | antiAdditive | antiMorphic =>
    exact iff_of_false (fun hc ↦ not_holds_toProjectivitySignature h hc.2) (by decide)

/-! ### The strengths a licenser carries and holds

The strengths a licenser carries form a lower set of the chain of strengths, and so do those it
holds outright, so each set is fixed by its greatest element. These are taken in the chain extended
by a least element, for none, and a greatest, above every strength, where the requirement and the
blocker of a polarity item also live. -/

open scoped Classical in
/-- The greatest strength of negation a licenser carries, `⊥` if it carries none. -/
noncomputable def carried (L : Licenser) : WithBot (WithTop Negation.Strength) :=
  (Finset.univ.filter L.Carries).sup
    fun s ↦ ((s : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength))

open scoped Classical in
/-- The greatest strength of negation a licenser holds outright, `⊥` if it holds none. -/
noncomputable def held (L : Licenser) : WithBot (WithTop Negation.Strength) :=
  (Finset.univ.filter fun s : Negation.Strength ↦ L.Holds s.toProjectivitySignature).sup
    fun s ↦ ((s : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength))

private theorem coe_le_sup_filter_iff {P : Negation.Strength → Prop} [DecidablePred P]
    (hP : ∀ ⦃s t : Negation.Strength⦄, P s → t ≤ s → P t) :
    ((s : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength)) ≤
      (Finset.univ.filter P).sup (fun t ↦
        ((t : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength))) ↔ P s := by
  rw [Finset.le_sup_iff (WithBot.bot_lt_coe _)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, WithBot.coe_le_coe, WithTop.coe_le_coe]
  exact ⟨fun ⟨_, ht, hst⟩ ↦ hP ht hst, fun h ↦ ⟨s, h, le_rfl⟩⟩

private theorem sup_filter_lt_top (P : Negation.Strength → Prop) [DecidablePred P] :
    (Finset.univ.filter P).sup (fun t ↦
      ((t : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength))) < ⊤ :=
  (Finset.sup_lt_iff (WithBot.bot_lt_iff_ne_bot.2 (by simp))).2 fun _ _ ↦
    WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)

theorem coe_le_carried_iff :
    ((s : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength)) ≤ L.carried ↔
      L.Carries s := by
  classical
  unfold carried
  exact coe_le_sup_filter_iff fun _ _ h hts ↦ h.of_le hts

theorem coe_le_held_iff :
    ((s : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength)) ≤ L.held ↔
      L.Holds s.toProjectivitySignature := by
  classical
  unfold held
  exact coe_le_sup_filter_iff fun _ _ h hts ↦ Holds.toProjectivitySignature_of_le h hts

theorem carried_lt_top : L.carried < ⊤ := by
  classical
  unfold carried
  exact sup_filter_lt_top _

theorem held_lt_top : L.held < ⊤ := by
  classical
  unfold held
  exact sup_filter_lt_top _

/-- A non-trivial classical licenser carries what it holds. -/
theorem carried_classical {F : OperatorFamily} (hn : ¬ (classical F).IsStrawsonUE) :
    (classical F).carried = (classical F).held := by
  classical
  simp only [carried, held, carries_classical_iff, and_iff_left hn]

end Licenser

/-! ### Licensing -/

namespace Licenser

variable (L : Licenser) (e : PolarityItem)

/-- A context **licenses** an item when its licenser carries the item's licensor, licenses free
choice and the item is a free choice item, or licenses by relevance and the item is a weak negative
polarity item. -/
def Licenses : Prop :=
  (∃ r ∈ e.licensor, L.Carries r) ∨ (L.LicensesFreeChoice ∧ e.IsFCI) ∨
    (L.LicensesByRelevance ∧ e.licensor = some .weak)

/-- A context **anti-licenses** an item when its licenser holds outright, on its plain meaning, the
strength that blocks the item ([vanderwouden-1997]'s laws (180), [szabolcsi-2004]'s (42)). -/
def AntiLicenses : Prop := ∃ r ∈ e.antiLicensor, L.Holds r.toProjectivitySignature

/-- A context **admits** an item when it licenses the item, if the item needs licensing, and does
not anti-license it. -/
def Admits : Prop := (e.IsNPI ∨ e.IsFCI → L.Licenses e) ∧ ¬ L.AntiLicenses e

variable {L e} {e' : PolarityItem} {F : OperatorFamily} {r r' : Negation.Strength}

instance [DecidablePred L.Licenses] [DecidablePred L.AntiLicenses] : DecidablePred L.Admits :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem admits_iff_licenses (h : e.antiLicensor = none) (he : e.IsNPI ∨ e.IsFCI) :
    L.Admits e ↔ L.Licenses e := by
  simp [Admits, AntiLicenses, h, he]

theorem admits_iff_not_antiLicenses (hn : ¬ e.IsNPI) (hf : ¬ e.IsFCI) :
    L.Admits e ↔ ¬ L.AntiLicenses e := by
  simp [Admits, hn, hf]

theorem admits_of_carries (he : e.licensor = some r) (ha : e.antiLicensor = none)
    (h : L.Carries r) : L.Admits e :=
  (admits_iff_licenses ha (.inl (by simp [IsNPI, he]))).2 (.inl ⟨r, he, h⟩)

theorem admits_of_not_holds (he : e.licensor = none) (hf : ¬ e.IsFCI)
    (ha : e.antiLicensor = some r) (h : ¬ L.Holds r.toProjectivitySignature) : L.Admits e :=
  (admits_iff_not_antiLicenses (by simp [IsNPI, he]) hf).2 fun ⟨_, hr, hh⟩ ↦
    h (Option.some_inj.1 (hr.symm.trans ha) ▸ hh)

/-- An item needing a strength above weak, and not a free choice item, is licensed exactly by the
contexts whose licenser carries that strength. -/
theorem licenses_iff_carries (he : e.licensor = some r) (hr : r ≠ .weak) (hf : ¬ e.IsFCI) :
    L.Licenses e ↔ L.Carries r := by
  simp [Licenses, he, hr, hf]

theorem antiLicenses_iff_holds (he : e.antiLicensor = some r) :
    L.AntiLicenses e ↔ L.Holds r.toProjectivitySignature := by
  simp [AntiLicenses, he]

theorem Licenses.of_licensor_le (he : e.licensor = some r) (he' : e'.licensor = some r')
    (hr : r' ≤ r) (hf : e.IsFCI → e'.IsFCI) : L.Licenses e → L.Licenses e' := by
  rintro (⟨s, hs, hc⟩ | ⟨hc, hfc⟩ | ⟨hc, hw⟩)
  · obtain rfl : s = r := Option.some_inj.1 (hs.symm.trans he)
    exact .inl ⟨r', he', hc.of_le hr⟩
  · exact .inr (.inl ⟨hc, hf hfc⟩)
  · obtain rfl : r = .weak := Option.some_inj.1 (he.symm.trans hw)
    exact .inr (.inr ⟨hc, he'.trans (congrArg _ (Negation.Strength.le_weak_iff.1 hr))⟩)

/-- A non-trivial classical context blocks the positive polarity items of a strength exactly where
it licenses the negative polarity items of that strength, the mirror image of
[vanderwouden-1997]'s (181). -/
theorem antiLicenses_iff_licenses (hn : ¬ (classical F).IsStrawsonUE)
    (h : e.antiLicensor = e'.licensor) :
    (classical F).AntiLicenses e ↔ (classical F).Licenses e' := by
  simp only [AntiLicenses, Licenses, h, carries_classical_iff, and_iff_left hn, LicensesFreeChoice,
    LicensesByRelevance, false_and, or_false]

/-- A licensing context without the free-choice and the relevance routes licenses an item exactly
when it carries what the item needs. -/
theorem licenses_iff_requirement_le (hfc : ¬ L.LicensesFreeChoice)
    (hrel : ¬ L.LicensesByRelevance) : L.Licenses e ↔ e.IsNPI ∧ e.requirement ≤ L.carried := by
  rcases h : e.licensor with _ | r
  · simp [Licenses, IsNPI, hfc, hrel, h]
  · simp [Licenses, IsNPI, requirement, hfc, hrel, h, coe_le_carried_iff]

/-- A context blocks an item exactly when it holds what blocks the item. -/
theorem antiLicenses_iff_blocker_le : L.AntiLicenses e ↔ e.blocker ≤ L.held := by
  rcases h : e.antiLicensor with _ | r
  · simp [AntiLicenses, blocker, h, not_le.2 held_lt_top]
  · simp [AntiLicenses, blocker, h, coe_le_held_iff]

/-- A non-trivial classical context admits an item that is not a free choice item exactly when the
strength it carries lies between what the item needs and what blocks it; the rows of
[vanderwouden-1997]'s table (182) are the strengths and its columns the items' intervals. -/
theorem admits_iff_carried_mem_Ico (hn : ¬ (classical F).IsStrawsonUE) (hf : ¬ e.IsFCI) :
    (classical F).Admits e ↔ (classical F).carried ∈ Set.Ico e.requirement e.blocker := by
  rw [Set.mem_Ico, Admits, licenses_iff_requirement_le id id, antiLicenses_iff_blocker_le,
    ← carried_classical hn, not_le]
  rcases h : e.licensor with _ | r
  · simp [IsNPI, IsFCI, requirement, h, hf]
  · simp [IsNPI, h]

/-- An antimorphic context blocks every positive polarity item, [vanderwouden-1997]'s (169). -/
theorem antiLicenses_iff_isPPI (h : L.Holds .antiAddMult) : L.AntiLicenses e ↔ e.IsPPI :=
  ⟨fun ⟨r, hr, _⟩ ↦ Option.isSome_iff_exists.2 ⟨r, hr⟩, fun he ↦
    let ⟨r, hr⟩ := Option.isSome_iff_exists.1 he
    ⟨r, hr, h.toProjectivitySignature_of_le (t := .antiMorphic) le_top⟩⟩

end Licenser

end PolarityItem
