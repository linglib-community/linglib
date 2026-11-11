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

A *licenser* is the operator that a construction places over the position of a polarity item. It
is given as a family of operators indexed by whatever the construction leaves open, such as the
model, a restrictor, a bound, or an accessibility relation. A licenser is of one of five kinds. A
*classical* licenser is a map between bounded lattices. A *scalar* licenser is such a map that has
stronger scale-mates. A *Strawsonian* licenser is von Fintel's map into trivalent propositions.
The remaining kinds are a *modal* licenser and a wh-question. Following Gajewski, a licenser has a
plain meaning below the exhaustivity operator and a second meaning above it. The meaning above
the operator adds the *direct implicature* of the licenser, which is its exhaustification against
its stronger scale-mates. Only a scalar licenser has a direct implicature.

A context *licenses* a `PolarityItem` in one of three ways. Its licenser may carry the strength
of negation that the item requires. Its licenser may license free choice, in which case the item
must be a free choice item. Finally, its licenser may be a question, in which case the item must
be a weak negative polarity item. A context *anti-licenses* an item when its licenser holds the
blocking strength of the item outright. A non-trivial classical context [admits an item exactly
when the strength it carries lies in the interval of the
item](##PolarityItem.Licenser.admits_iff_carried_mem_Ico). Such a context [blocks the positive
polarity items of a strength exactly where it licenses the negative polarity items of that
strength](##PolarityItem.Licenser.antiLicenses_iff_licenses), and an antimorphic context [blocks
every positive polarity item](##PolarityItem.Licenser.antiLicenses_iff_isPPI).

## Main definitions

* `PolarityItem.Licenser`: the five kinds of licenser.
* `PolarityItem.Licenser.exhaustified`: the meaning of a licenser above the exhaustivity operator,
  with its direct implicature added.
* `PolarityItem.Licenser.Holds`, `PolarityItem.Licenser.IsStrawsonDE`,
  `PolarityItem.Licenser.IsStrawsonUE`: a signature that a licenser holds outright, and downward
  and upward entailment modulo presupposition.
* `PolarityItem.Licenser.Carries`: a strength of negation that a licenser carries. Von Fintel
  requires the plain meaning to be downward entailing modulo presupposition, and Bylinina and
  Nouwen add that it must not be upward entailing as well. A strength above weak must in addition
  hold outright of the exhaustified meaning.
* `PolarityItem.Licenser.LicensesByStrengthening`, `PolarityItem.Licenser.LicensesFreeChoice`,
  `PolarityItem.Licenser.LicensesByRelevance`: the three routes of licensing. A downward-entailing
  licenser licenses by strengthening, after Kadmon and Landman, a modal licenser licenses by free
  choice, after Chierchia, and a question licenses by relevance, after van Rooy.
* `PolarityItem.Licenser.Licenses`, `PolarityItem.Licenser.AntiLicenses`,
  `PolarityItem.Licenser.Admits`: the licensing relations between a licenser and an item.

## Main statements

* `PolarityItem.Licenser.licensesByStrengthening_iff`: widening the domain strengthens under a
  licenser exactly when the licenser is downward entailing modulo presupposition.

## Implementation notes

* Licensing is evaluated on the meaning modulo presupposition and with its direct implicature,
  following von Fintel and Gajewski. Anti-licensing is evaluated on the plain meaning, as van der
  Wouden and Szabolcsi state it. On their account, presuppositional operators such as *only* and
  *regret* rescue a positive polarity item instead of blocking it.
* Gajewski requires only that the exhaustified meaning be downward entailing. Zwarts's strengths
  are retained here, and they agree with Gajewski's condition at the endpoints of the scale.
* The unit conditions of `ProjectivitySignature.HoldsFor` do not exclude constant maps. A constant
  map is downward entailing, and a constantly false map is anti-additive. The requirement that
  weak strength not be upward entailing as well excludes them, since a map that is monotone in
  both directions modulo presupposition takes a single value at comparable arguments where it is
  defined (`Presupposition.isStrawsonUE_and_isStrawsonDE_iff`).
* The question route states the weak form that the theory of question value proves, namely that
  widening the domain never lowers the value of the question. Van Rooy's strict condition for
  rhetorical questions is not formalized.

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

/-- A family of operators on a scale with stronger scale-mates. Each operator is paired with its
meaning enriched by its direct implicature, which is its exhaustification against those
scale-mates ([gajewski-2011]'s `O` with `ALT-1`). -/
structure ScalarFamily extends OperatorFamily where
  /-- The operator exhaustified against its stronger scale-mates, at each parameter. -/
  exhaustified : ∀ p, Dom p → Cod p

end Licenser

/-- The operator that a construction places over the position of a polarity item. It is
classical, scalar with its enrichment, a map into trivalent propositions, modal, or a question. -/
inductive Licenser : Type 2 where
  | classical (F : Licenser.OperatorFamily)
  | scalar (F : Licenser.ScalarFamily)
  | strawson (F : Licenser.PresupposingFamily)
  | modal (F : Licenser.ModalFamily)
  | question

/-- The route by which a context licenses polarity items. A context licenses by strengthening, as
a generic context that licenses free choice items ([kadmon-landman-1993], [dayal-1996]), or by
the relevance of a question ([van-rooy-2003-npi]). -/
inductive LicensingMechanism where
  | strengthening
  | genericIndefinite
  | entropy
  deriving DecidableEq, Repr

namespace Licenser

/-- The meaning of a licenser above the exhaustivity operator. A scalar licenser takes the meaning
of its enriched operators, and any other licenser keeps its own meaning. -/
def exhaustified : Licenser → Licenser
  | .scalar F => .classical { F.toOperatorFamily with op := F.exhaustified }
  | L => L

/-- A licenser *holds* a signature outright when every operator in its family does. An operator
into trivalent propositions holds the signature on its truth set, and a scalar operator holds it
on its plain meaning. -/
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
modulo its presupposition. A constant operator is both upward and downward entailing. -/
def IsStrawsonUE : Licenser → Prop
  | .classical F | .scalar ⟨F, _⟩ => ∀ p, Monotone (F.op p)
  | .strawson F => ∀ p, Presupposition.IsStrawsonUE (F.op p)
  | .modal F => ∀ p, Monotone (F.op p)
  | .question => False

/-- A licenser *carries* weak strength when it is downward entailing and not upward entailing
modulo presupposition. This is the condition that [von-fintel-1999], [gajewski-2011]'s Condition
1, and [bylinina-nouwen-2018]'s (53) place on the meaning below the exhaustivity operator. A
licenser carries a stronger strength when, in addition, its exhaustified meaning holds that
strength outright. -/
def Carries (L : Licenser) : Negation.Strength → Prop
  | .weak => L.IsStrawsonDE ∧ ¬ L.IsStrawsonUE
  | s => (L.IsStrawsonDE ∧ ¬ L.IsStrawsonUE) ∧ L.exhaustified.Holds s.toProjectivitySignature

section OfOperator

variable {σ P : Type} [Lattice σ] [BoundedOrder σ] [Lattice P] [BoundedOrder P] {f : σ → P}
  {s : Negation.Strength}

/-- The classical licenser of a single operator over the position of a polarity item. -/
def ofOperator (f : σ → P) : Licenser :=
  .classical { Param := PUnit, Dom := fun _ ↦ σ, Cod := fun _ ↦ P, op := fun _ ↦ f }

/-- A single operator carries a strength of negation exactly when it is in the function class of
the strength and is not upward entailing. -/
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
  | .question => False

/-- A modal licenser *licenses free choice* when the antiexhaustified existential is consistent
under one of its operators, over a domain of at least two possible witnesses
([chierchia-2006]). -/
def LicensesFreeChoice : Licenser → Prop
  | .modal F => ∃ p, ∃ (E : Type) (P : E → Set (F.W p)) (D : Finset E), 1 < D.card ∧
      (antiExh (fun S ↦ F.op p (⋃ a ∈ S, P a)) D).Nonempty
  | .classical _ | .scalar _ | .strawson _ | .question => False

/-- A question *licenses by relevance* an item that widens its domain, since widening the domain
of a wh-question never lowers its value in any decision problem ([van-rooy-2003-npi]). -/
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

/-- Widening the domain strengthens under every operator of a licenser exactly when the licenser
is downward entailing modulo presupposition. -/
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

/-- A classical licenser carries a strength exactly when it holds that strength outright and is
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

/-- A non-trivial classical licenser that holds exactly the strengths up to `s₀` carries exactly
those strengths. -/
theorem carries_classical_iff_le {F : OperatorFamily} {s₀ : Negation.Strength}
    (hn : ¬ (classical F).IsStrawsonUE)
    (h : ∀ s, (classical F).Holds s.toProjectivitySignature ↔ s ≤ s₀) :
    (classical F).Carries s ↔ s ≤ s₀ := by
  rw [carries_classical_iff, h, and_iff_left hn]

/-- A non-trivial licenser that is downward entailing modulo presupposition and holds exactly the
strengths up to `s₀` once exhaustified carries exactly those strengths. -/
theorem carries_iff_le {s₀ : Negation.Strength} (hde : L.IsStrawsonDE) (hn : ¬ L.IsStrawsonUE)
    (h : ∀ s, L.exhaustified.Holds s.toProjectivitySignature ↔ s ≤ s₀) : L.Carries s ↔ s ≤ s₀ := by
  cases s with
  | weak => exact iff_of_true ⟨hde, hn⟩ (Negation.Strength.weak_le _)
  | antiAdditive | antiMorphic => exact (and_iff_right ⟨hde, hn⟩).trans (h _)

/-- A presupposing licenser carries anti-additive strength when its truth sets are anti-additive
and empty at the trivial argument, and one of its operators is not upward entailing. -/
theorem carries_strawson_antiAdditive {F : PresupposingFamily}
    (h : ∀ p, IsAntiAdditive fun x ↦ Trivalent.posExt (F.op p x))
    (ht : ∀ p, Trivalent.posExt (F.op p ⊤) = ⊥)
    (hn : ∃ p, ¬ Presupposition.IsStrawsonUE (F.op p)) : (strawson F).Carries .antiAdditive :=
  have hh : (strawson F).Holds .antiAdd := fun p ↦
    ProjectivitySignature.holdsFor_antiAdd_iff.2 ⟨h p, ht p⟩
  ⟨⟨isStrawsonDE_of_holds_anti (hh.of_le (by decide)), fun hu ↦ hn.elim fun p hp ↦ hp (hu p)⟩, hh⟩

theorem not_carries_strawson_antiAdditive {F : PresupposingFamily}
    (h : ∃ p, ¬ IsAntiAdditive fun x ↦ Trivalent.posExt (F.op p x)) :
    ¬ (strawson F).Carries .antiAdditive :=
  fun hc ↦ h.elim fun p hp ↦ hp (ProjectivitySignature.holdsFor_antiAdd_iff.1 (hc.2 p)).1

theorem holds_toProjectivitySignature_iff {s₀ : Negation.Strength}
    (h : L.Holds s₀.toProjectivitySignature)
    (hn : ∀ s, s₀ < s → ¬ L.Holds s.toProjectivitySignature) :
    L.Holds s.toProjectivitySignature ↔ s ≤ s₀ :=
  ⟨fun hs ↦ not_lt.mp fun hlt ↦ hn s hlt hs, fun hs ↦ h.toProjectivitySignature_of_le hs⟩

theorem not_holds_toProjectivitySignature (h : ¬ L.Holds .anti) :
    ¬ L.Holds s.toProjectivitySignature := fun hs ↦
  h (hs.of_le (Negation.Strength.toProjectivitySignature_antitone bot_le))

/-- A non-trivial licenser that is downward entailing modulo presupposition, but not downward
entailing outright once its direct implicature is added, carries exactly weak strength
([gajewski-2011]). -/
theorem carries_iff_eq_weak (hde : L.IsStrawsonDE) (hn : ¬ L.IsStrawsonUE)
    (h : ¬ L.exhaustified.Holds .anti) : L.Carries s ↔ s = .weak := by
  cases s with
  | weak => exact iff_of_true ⟨hde, hn⟩ rfl
  | antiAdditive | antiMorphic =>
    exact iff_of_false (fun hc ↦ not_holds_toProjectivitySignature h hc.2) (by decide)

/-! ### The strengths a licenser carries and holds

The strengths that a licenser carries form a lower set of the chain of strengths, and so do the
strengths that it holds outright. Each set is therefore determined by its greatest element. The
greatest element is taken in the chain extended by a least element, which stands for no strength,
and by a greatest element above every strength. The requirement and the blocker of a polarity
item are taken in the same extended chain. -/

open scoped Classical in
/-- The greatest strength of negation that a licenser carries, or `⊥` if it carries none. -/
noncomputable def carried (L : Licenser) : WithBot (WithTop Negation.Strength) :=
  (Finset.univ.filter L.Carries).sup
    fun s ↦ ((s : WithTop Negation.Strength) : WithBot (WithTop Negation.Strength))

open scoped Classical in
/-- The greatest strength of negation that a licenser holds outright, or `⊥` if it holds none. -/
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

/-- A non-trivial classical licenser carries exactly the strengths that it holds. -/
theorem carried_classical {F : OperatorFamily} (hn : ¬ (classical F).IsStrawsonUE) :
    (classical F).carried = (classical F).held := by
  classical
  simp only [carried, held, carries_classical_iff, and_iff_left hn]

end Licenser

/-! ### Licensing -/

namespace Licenser

variable (L : Licenser) (e : PolarityItem)

/-- A context **licenses** an item in one of three cases. Its licenser carries the licensor of the
item, its licenser licenses free choice and the item is a free choice item, or its licenser
licenses by relevance and the item is a weak negative polarity item. -/
def Licenses : Prop :=
  (∃ r ∈ e.licensor, L.Carries r) ∨ (L.LicensesFreeChoice ∧ e.IsFCI) ∨
    (L.LicensesByRelevance ∧ e.licensor = some .weak)

/-- A context **anti-licenses** an item when its licenser holds the strength that blocks the item
outright, on its plain meaning ([vanderwouden-1997]'s laws (180), [szabolcsi-2004]'s (42)). -/
def AntiLicenses : Prop := ∃ r ∈ e.antiLicensor, L.Holds r.toProjectivitySignature

/-- A context **admits** an item when it does not anti-license the item and, if the item requires
licensing, licenses it. -/
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

/-- An item that requires a strength above weak and is not a free choice item is licensed exactly
by the contexts whose licenser carries that strength. -/
theorem licenses_iff_carries (he : e.licensor = some r) (hr : r ≠ .weak) (hf : ¬ e.IsFCI) :
    L.Licenses e ↔ L.Carries r := by
  simp [Licenses, he, hr, hf]

/-- An item that only requires a strength above weak is admitted exactly by the contexts whose
licenser carries that strength. -/
theorem admits_iff_carries (he : e.licensor = some r) (hr : r ≠ .weak)
    (ha : e.antiLicensor = none) (hf : ¬ e.IsFCI) : L.Admits e ↔ L.Carries r :=
  (admits_iff_licenses ha (.inl (by simp [IsNPI, he]))).trans (licenses_iff_carries he hr hf)

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
it licenses the negative polarity items of that strength. This is the mirror image of
[vanderwouden-1997]'s (181). -/
theorem antiLicenses_iff_licenses (hn : ¬ (classical F).IsStrawsonUE)
    (h : e.antiLicensor = e'.licensor) :
    (classical F).AntiLicenses e ↔ (classical F).Licenses e' := by
  simp only [AntiLicenses, Licenses, h, carries_classical_iff, and_iff_left hn, LicensesFreeChoice,
    LicensesByRelevance, false_and, or_false]

/-- A licensing context that has neither the free-choice route nor the relevance route licenses an
item exactly when it carries the strength that the item requires. -/
theorem licenses_iff_requirement_le (hfc : ¬ L.LicensesFreeChoice)
    (hrel : ¬ L.LicensesByRelevance) : L.Licenses e ↔ e.IsNPI ∧ e.requirement ≤ L.carried := by
  rcases h : e.licensor with _ | r
  · simp [Licenses, IsNPI, hfc, hrel, h]
  · simp [Licenses, IsNPI, requirement, hfc, hrel, h, coe_le_carried_iff]

/-- A context blocks an item exactly when it holds the strength that blocks the item. -/
theorem antiLicenses_iff_blocker_le : L.AntiLicenses e ↔ e.blocker ≤ L.held := by
  rcases h : e.antiLicensor with _ | r
  · simp [AntiLicenses, blocker, h, not_le.2 held_lt_top]
  · simp [AntiLicenses, blocker, h, coe_le_held_iff]

/-- A non-trivial classical context admits an item that is not a free choice item exactly when the
strength it carries lies between the strength that the item requires and the strength that blocks
it. The rows of [vanderwouden-1997]'s table (182) are the strengths, and its columns are the
intervals of the items. -/
theorem admits_iff_carried_mem_Ico (hn : ¬ (classical F).IsStrawsonUE) (hf : ¬ e.IsFCI) :
    (classical F).Admits e ↔ (classical F).carried ∈ Set.Ico e.requirement e.blocker := by
  rw [Set.mem_Ico, Admits, licenses_iff_requirement_le id id, antiLicenses_iff_blocker_le,
    ← carried_classical hn, not_le]
  rcases h : e.licensor with _ | r
  · simp [IsNPI, IsFCI, requirement, h, hf]
  · simp [IsNPI, h]

/-- An antimorphic context blocks every positive polarity item, which is [vanderwouden-1997]'s
(169). -/
theorem antiLicenses_iff_isPPI (h : L.Holds .antiAddMult) : L.AntiLicenses e ↔ e.IsPPI :=
  ⟨fun ⟨r, hr, _⟩ ↦ Option.isSome_iff_exists.2 ⟨r, hr⟩, fun he ↦
    let ⟨r, hr⟩ := Option.isSome_iff_exists.1 he
    ⟨r, hr, h.toProjectivitySignature_of_le (t := .antiMorphic) le_top⟩⟩

end Licenser

end PolarityItem
