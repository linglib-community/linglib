/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Exhaustification.Basic
public import Linglib.Semantics.PolarityItem.Basic
public import Linglib.Semantics.PolarityItem.Licenser
public import Linglib.Semantics.Embedding.NegRaising.Basic
public import Linglib.Semantics.Embedding.Preference.BestWorlds
public import Linglib.Semantics.Conditionals.Horizon
public import Linglib.Semantics.Degree.Superlative
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Tense.Since
public import Linglib.Semantics.Quantifier.Counting
public import Linglib.Semantics.Quantifier.Defs
public import Linglib.Semantics.Quantifier.Projectivity
public import Linglib.Semantics.Reference.Indefinite
public import Linglib.Semantics.Tense.Before
public import Mathlib.Basic.Rel

/-!
# Licensing contexts

A *licensing context* is a construction that can host a polarity item. It places a licenser over
the position of the item, and it realizes a function of Haspelmath's implicational map when it
realizes one. The strength of negation that its licenser carries is a theorem about the operators
that the construction denotes. Clausal negation is anti-morphic. *Nobody*, the restrictors of a
universal and of *no*, *without*, *deny*, negation over a neg-raising attitude, *before*,
*too … to*, and the clausal comparative are anti-additive and no stronger, and *doubt* is downward
entailing and no stronger. Each of these except *before* has its strength because it composes
negation with a positive operator that is not additive. *Few* and *at most* are scalar. They are
downward entailing, but they are no longer downward entailing once they are exhaustified against
the stronger *no* and *at most n − 1*, which is the determiner exhaustification
`Quantifier.Det.exhaustified`. Every downward entailing context is downward entailing
non-trivially, and not merely by being constant. Focus *only*, adversatives, superlatives,
conditional antecedents, and temporal *since* are downward entailing only modulo their
presuppositions. The modals, imperatives, generics, and free relatives are modal licensers, and
a question licenses no item. A positive assertion places the identity over the item. A study may
state the theory of a licenser of its own. The named constructions are the shared inventory that
lexical entries cite.

## Main declarations

* `PolarityItem.LicensingContext.licenser`, `PolarityItem.LicensingContext.haspelmath`: the
  operator that a construction other than a question places over the item, and the function of
  Haspelmath's map that the construction realizes.
* `Quantifier.Det.exhaustified`: a determiner exhaustified against its scale-mates.
* `PolarityItem.LicensingContext.profile`: the strengths that a construction carries and holds,
  as a table, with `PolarityItem.LicensingContext.profile_eq` that it is the profile of the
  licenser.
* `PolarityItem.Class.region`, `PolarityItem.Compatible`: the contexts in which a class is
  predicted to be possible, and an entry whose contexts agree with that prediction.
* `PolarityItem.LicensingContext.holds_negation`, `holds_nobody_iff`, `not_isStrawsonUE_nobody`,
  `not_holds_exhaustified_few`, …: the certificates of the licenser of each context, from which
  its profile is proved.

## Implementation notes

* A context is a name. A study that links an example to the context in which it stands therefore
  links computable data with decidable equality, while the licenser, which is often defined
  classically, is a function of the name. Distinct constructions can share a licenser. The
  necessity modal, the imperative, the generic, and the free relative are all necessities. The
  clausal comparative and *too … to* both place the compared individual above the degrees of the
  clause, and *deny* asserts, as negation over a neg-raising attitude presupposes and asserts,
  that the attitude holds
  of the negated complement.
* The inventory consists of the contexts to which the library gives a semantics, and it is not an
  exhaustive list. It realizes seven of Haspelmath's nine functions, with the necessity modal and
  the imperative realizing the irrealis non-specific function. Many licensers of the literature on
  downward entailment are still missing, such as negative adverbs, *neither … nor*, and
  *not every*.
* *Before* receives Anscombe's universal reading, *before ever*. *Too … to* states that the degree
  of the subject exceeds every degree at which the infinitive holds, after Meier. *Doubt* is
  analysed as not believing the complement, and *deny* as asserting its negation, each over a
  doxastic or assertoric accessibility relation.
* The free relative is read as a necessity over its alternatives, with the modal presupposition of
  *-ever*. The generic is read as a necessity over normal worlds.
* The placements on Haspelmath's map are those of his book. *Nobody*, *before*-clauses, and
  adversatives sit between direct and indirect negation there, so they realize no function here.
  The constructions outside the inventory of the map realize no function either.

## References

* [ladusaw-1979]
* [zwarts-1998]
* [vanderwouden-1997]
* [von-fintel-1999]
* [gajewski-2011]
* [bylinina-nouwen-2018]
* [anscombe-1964]
* [hoeksema-1983]
* [meier-2003]
* [chierchia-2006]
* [kadmon-landman-1993]
* [van-rooy-2003a]
* [haspelmath-1997]
* [gajewski-2007]
-/

@[expose] public section

/-! ### Determiners exhaustified against their scale-mates -/

namespace Quantifier.Det

variable {α : Type*} {Q Q' : Det α} {C : Set (Det α)} {A P : Set α}

/-- The determiner `Q` exhaustified against its scale-mates `C`. At each restrictor, it holds of
the scopes at which `Q` holds and every scale-mate that holds there is entailed by `Q`. Entailment
is evaluated with the restrictor fixed and quantifies over scopes ([gajewski-2011]'s `O` with
`ALT-1`). -/
def exhaustified (Q : Det α) (C : Set (Det α)) : Det α :=
  fun A P ↦ P ∈ Exhaustification.exh ((fun Q' : Det α ↦ {P | Q' A P}) '' C) {P | Q A P}

theorem exhaustified_iff : exhaustified Q C A P ↔ Q A P ∧ ∀ Q' ∈ C, Q' A P → Q A ≤ Q' A :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨h, fun Q' hQ' hP ↦ h' _ ⟨Q', hQ', rfl⟩ hP⟩,
    fun ⟨h, h'⟩ ↦ ⟨h, by rintro _ ⟨Q', hQ', rfl⟩ hP; exact h' Q' hQ' hP⟩⟩

theorem not_exhaustified_of_not_le (hQ' : Q' ∈ C) (hP : Q' A P) (h : ¬ Q A ≤ Q' A) :
    ¬ exhaustified Q C A P :=
  fun he ↦ h ((exhaustified_iff.1 he).2 Q' hQ' hP)

theorem exhaustified_eq_of_forall_le (h : ∀ Q' ∈ C, ∀ P, Q' A P → Q A ≤ Q' A) :
    exhaustified Q C A = Q A :=
  funext fun P ↦ congrArg (P ∈ ·) (Exhaustification.exh_eq_self_iff.2
    (by rintro _ ⟨Q', hQ', rfl⟩ ⟨P, _, hP⟩; exact h Q' hQ' P hP))

theorem exhaustified_no : exhaustified (no : Det α) {everyᶜ} = no := by
  funext A
  refine exhaustified_eq_of_forall_le fun Q' hQ' P hP ↦ ?_
  rw [Set.mem_singleton_iff] at hQ'
  subst hQ'
  obtain ⟨x, hx, -⟩ := Set.not_subset.1 hP
  exact fun _ hno hev ↦ hno hx (hev hx)

end Quantifier.Det

namespace PolarityItem

open NaturalLogic Presupposition Quantifier Quantifier.Det Tense Indefinite

/-- The function of [haspelmath-1997]'s implicational map that a construction realizes, if any.
The necessity modal and the imperative are irrealis non-specific environments. The book finds
free-choice items unacceptable under necessity, in contrast to possibility, and acceptable in
imperatives only when the imperative is read as a permission. -/
def LicensingContext.haspelmath : LicensingContext → Option HaspelmathFunction
  | negation => some .directNeg
  | withoutClause | doubtVerb | denyVerb | superordinateNegation => some .indirectNeg
  | clausalComparative => some .comparative
  | conditionalAntecedent => some .conditional
  | polarQuestion | constituentQuestion => some .question
  | modalNecessity | imperative => some .irrealis
  | modalPossibility | generic | freeRelative => some .freeChoice
  | positiveAssertion | nobody | few | atMost | universalRestrictor | noRestrictor | beforeClause
  | tooTo | onlyFocus | adversative | superlative | sinceTemporal => none

namespace LicensingContext

/-! ### The parameters of the operator families -/

/-- A domain of individuals and a predicate over it. -/
structure Predicate where
  /-- The individuals. -/
  ι : Type
  /-- The predicate. -/
  A : Set ι

/-- A finite domain and a predicate over it. -/
structure FinitePredicate extends Predicate where
  /-- The domain is finite. -/
  [fin : Fintype ι]

attribute [instance] FinitePredicate.fin

/-- A predicate that is true of something, as the restrictor of a negative quantifier is. -/
structure NonemptyPredicate extends Predicate where
  nonempty : A.Nonempty

/-- A predicate that is false of something, as the scope of a universal is. -/
structure NonuniversalPredicate extends Predicate where
  nonuniversal : ∃ x, x ∉ A

/-- A finite predicate together with a bound, as the restrictor of *at most n* is. -/
structure BoundedPredicate extends FinitePredicate where
  /-- The bound. -/
  n : ℕ

/-- A time line and the run times of a main clause. -/
structure MainClause where
  /-- The times. -/
  T : Type
  /-- The times are linearly ordered. -/
  [ord : LinearOrder T]
  /-- The run times of the main clause. -/
  A : NonemptyInterval T → Prop

attribute [instance] MainClause.ord

/-- A measure of individuals on a linearly ordered scale, and the individual compared. -/
structure Measured where
  /-- The individuals. -/
  E : Type
  /-- The degrees. -/
  D : Type
  /-- The degrees are linearly ordered. -/
  [ord : LinearOrder D]
  /-- The measure. -/
  μ : E → D
  /-- The individual compared. -/
  x : E

attribute [instance] Measured.ord

/-- An accessibility relation over worlds, and the evaluation world. -/
structure Accessibility where
  /-- The worlds. -/
  W : Type
  /-- The accessibility relation. -/
  R : SetRel W W
  /-- The evaluation world. -/
  w : W

/-- An accessibility relation with a world accessible from the evaluation world. -/
structure SerialAccessibility extends Accessibility where
  serial : ∃ v, (w, v) ∈ R

/-- The modal base of a neg-raising attitude and the alternatives into which the presupposition
of its complement projects. -/
structure Bases where
  /-- The worlds. -/
  W : Type
  /-- The modal base. -/
  R : SetRel W W
  /-- The alternatives into which the presupposition of the complement projects. -/
  H : SetRel W W

/-- An accessibility relation over worlds. -/
structure Frame where
  /-- The worlds. -/
  W : Type
  /-- The accessibility relation. -/
  R : SetRel W W

/-- A focused individual among others, over worlds. -/
structure Focus where
  /-- The individuals. -/
  ι : Type
  /-- The worlds. -/
  W : Type
  /-- The focused individual. -/
  x : ι

/-- The doxastic state, the domain, and the ordering source of an adversative attitude. -/
structure Attitude where
  /-- The worlds. -/
  W : Type
  /-- The doxastic state. -/
  dox : W → Set W
  /-- The domain. -/
  base : W → Set W
  /-- The ordering source. -/
  g : W → Set (Set W)

/-- A measure of the members of a comparison class, and the individual described. -/
structure Superlative where
  /-- The individuals. -/
  α : Type
  /-- The worlds. -/
  W : Type
  /-- The degrees. -/
  D : Type
  /-- The degrees are preordered. -/
  [pre : Preorder D]
  /-- The measure. -/
  μ : α → D
  /-- The individual described. -/
  x : α

attribute [instance] Superlative.pre

/-- The modal horizon and the consequent of a counterfactual. -/
structure Horizon where
  /-- The evaluation indices. -/
  I : Type
  /-- The worlds. -/
  W : Type
  /-- The modal horizon. -/
  horizon : I → Set W
  /-- The consequent. -/
  q : Set W

/-- A time line and the shift back to the reference time of *since*. -/
structure Ago where
  /-- The times. -/
  T : Type
  /-- The times are linearly ordered. -/
  [ord : LinearOrder T]
  /-- The shift back. -/
  ago : T → T

attribute [instance] Ago.ord

/-! ### The licensers of the contexts -/

/-- The family of operators stating that the compared individual exceeds every degree of a
clause. -/
abbrev exceedsFamily : Licenser.OperatorFamily :=
  ⟨Measured, fun p ↦ Set p.D, fun _ ↦ Prop, fun p Δ ↦ p.μ p.x ∈ strictUpperBounds Δ⟩

/-- Necessity over a frame. -/
abbrev necessityFamily : Licenser.ModalFamily := ⟨Frame, fun p ↦ p.W, fun p ↦ p.R.core⟩

/-- A construction places an operator over the position of a polarity item, unless it is a
question. -/
def HasLicenser : LicensingContext → Prop
  | polarQuestion | constituentQuestion => False
  | _ => True

instance : DecidablePred HasLicenser := fun c ↦ by
  cases c <;> first | exact isTrue trivial | exact isFalse id

/-- The licenser that a construction places over the position of a polarity item. -/
noncomputable def licenser : (c : LicensingContext) → (_ : c.HasLicenser := by decide) → Licenser
  | negation, _ => .classical ⟨Type, fun α ↦ α → Prop, fun α ↦ α → Prop, fun _ ↦ compl⟩
  | nobody, _ => .classical ⟨NonemptyPredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p ↦ Det.no p.A⟩
  | few, _ => .scalar ⟨⟨FinitePredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p ↦ Det.few p.A⟩,
      fun p ↦ Det.exhaustified Det.few {Det.no} p.A⟩
  | atMost, _ => .scalar
      ⟨⟨BoundedPredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p ↦ Det.atMost p.n p.A⟩,
        fun p ↦ Det.exhaustified (Det.atMost p.n) {Det.atMost (p.n - 1)} p.A⟩
  | universalRestrictor, _ => .classical
      ⟨NonuniversalPredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p R ↦ Det.every R p.A⟩
  | noRestrictor, _ => .classical
      ⟨NonemptyPredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p R ↦ Det.no R p.A⟩
  | withoutClause, _ => .classical
      ⟨Predicate, fun p ↦ Set p.ι, fun p ↦ Set p.ι, fun p V ↦ p.A \ V⟩
  | beforeClause, _ => .classical
      ⟨MainClause, fun p ↦ NonemptyInterval p.T → Prop, fun _ ↦ Prop, fun p ↦ beforeEver p.A⟩
  | clausalComparative, _ | tooTo, _ => .classical exceedsFamily
  | doubtVerb, _ => .classical
      ⟨Accessibility, fun p ↦ Set p.W, fun _ ↦ Prop, fun p P ↦ p.w ∉ p.R.core P⟩
  | denyVerb, _ => .classical
      ⟨SerialAccessibility, fun p ↦ Set p.W, fun _ ↦ Prop, fun p P ↦ p.w ∈ p.R.core Pᶜ⟩
  | superordinateNegation, _ => .strawson
      ⟨Bases, fun p ↦ Set p.W, fun p ↦ p.W, fun p ↦ NegRaising.negation p.R p.H⟩
  | onlyFocus, _ => .strawson ⟨Focus, fun p ↦ p.ι → Set p.W, fun p ↦ p.W,
      fun p P ↦ Focus.only (· = ·) Set.univ P p.x⟩
  | adversative, _ => .strawson ⟨Attitude, fun p ↦ Set p.W, fun p ↦ p.W,
      fun p ↦ Desire.BestWorlds.regret p.dox p.base p.g⟩
  | superlative, _ => .strawson ⟨Superlative, fun p ↦ p.W → Set p.α, fun p ↦ p.W,
      fun p C ↦ trivalentSuperlative p.μ C p.x⟩
  | conditionalAntecedent, _ => .strawson ⟨Horizon, fun p ↦ Set p.W, fun p ↦ p.I,
      fun p P ↦ Conditional.horizonCounterfactual p.horizon P p.q⟩
  | sinceTemporal, _ => .strawson ⟨Ago, fun p ↦ Set p.T, fun p ↦ p.T, fun p ↦ since p.ago⟩
  | positiveAssertion, _ => .classical ⟨Type, fun α ↦ α → Prop, fun α ↦ α → Prop, fun _ ↦ id⟩
  | polarQuestion, h | constituentQuestion, h => h.elim
  | modalPossibility, _ => .modal ⟨Frame, fun p ↦ p.W, fun p ↦ p.R.preimage⟩
  | modalNecessity, _ | imperative, _ | generic, _ | freeRelative, _ => .modal necessityFamily

/-! ### Classical licensers

Six of the classical licensers are a positive operator composed with negation. *Nobody*, the
restrictor of a universal, the clausal comparative, and *too … to* are the scope of a universal
applied after negation, over individuals or degrees. *Deny* is necessity applied after negation,
*without* is a meet applied after negation, and *doubt* is negation applied after necessity. Each
holds the strengths dual to the classes of its positive operator
(`Negation.Strength.forall_holdsFor_iff_le_antiAdditive`). Since the scope of a universal,
necessity, and a meet are multiplicative and not additive, each of these licensers is
anti-additive and no stronger, except *doubt*, which is downward entailing and no stronger. -/

private theorem holdsFor_mult_mem_core {W : Type} {R : SetRel W W} {w : W} (h : ∃ v, (w, v) ∈ R) :
    ProjectivitySignature.mult.HoldsFor fun P ↦ w ∈ R.core P :=
  ProjectivitySignature.holdsFor_mult_iff.2
    ⟨fun _ _ ↦ by simp [SetRel.core_inter], eq_false fun hw ↦ h.elim fun _ hv ↦ hw hv⟩

private theorem holdsFor_mono_mem_core {W : Type} {R : SetRel W W} {w : W} :
    ProjectivitySignature.mono.HoldsFor fun P ↦ w ∈ R.core P :=
  ProjectivitySignature.holdsFor_mono_iff.2 fun _ _ hPQ hP ↦ SetRel.core_mono hPQ hP

/-- Necessity is not additive at a world that accesses two worlds. -/
private theorem not_holdsFor_additive_mem_core :
    ¬ ProjectivitySignature.additive.HoldsFor
      fun P ↦ true ∈ SetRel.core (.univ : SetRel Bool Bool) P :=
  fun h ↦ by
    have := eq_iff_iff.1 ((ProjectivitySignature.holdsFor_additive_iff.1 h).1 {true} {false})
    simp only [SetRel.mem_core, Set.mem_union, Set.mem_singleton_iff,
      sup_Prop_eq] at this
    exact (this.1 fun b _ ↦ by cases b <;> simp).elim
      (fun h ↦ absurd (h (b := false) trivial) (by decide))
      fun h ↦ absurd (h (b := true) trivial) (by decide)

private theorem holdsFor_mult_inf_left {ι : Type} (A : Set ι) :
    ProjectivitySignature.mult.HoldsFor (A ⊓ ·) :=
  ProjectivitySignature.holdsFor_mult_iff.2 ⟨fun _ _ ↦ inf_inf_distrib_left _ _ _, inf_bot_eq A⟩

open Licenser

theorem holds_negation (s : Negation.Strength) :
    negation.licenser.Holds s.toProjectivitySignature :=
  (show negation.licenser.Holds .antiAddMult from fun _ ↦
    ProjectivitySignature.holdsFor_antiAddMult_compl).toProjectivitySignature_of_le
      (s := s) (t := .antiMorphic) le_top

theorem holds_nobody_iff {s : Negation.Strength} :
    nobody.licenser.Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive :=
  Negation.Strength.forall_holdsFor_iff_le_antiAdditive (g := fun p : NonemptyPredicate ↦
    Det.every p.A) (fun _ ↦ rfl) (fun p ↦ holdsFor_mult_every p.nonempty)
    ⟨⟨⟨Bool, .univ⟩, Set.univ_nonempty⟩, not_holdsFor_additive_every (a := true) (b := false)
      trivial trivial (by decide)⟩

theorem holds_few_iff {s : Negation.Strength} :
    few.licenser.Holds s.toProjectivitySignature ↔ s ≤ .weak := by
  refine holds_toProjectivitySignature_iff (fun p ↦ ProjectivitySignature.holdsFor_anti_iff.mpr
    (scopeAntitone_few p.A))
    fun s hs h ↦ ?_
  have := (ProjectivitySignature.holdsFor_antiAdd_iff.mp
    ((h.toProjectivitySignature_of_le (s := .antiAdditive)
    (by revert hs; cases s <;> decide)) ⟨⟨Fin 3, Set.univ⟩⟩)).1 {0} {1}
  revert this
  show Det.few (Set.univ : Set (Fin 3)) ({0} ∪ {1}) = (_ ∧ _) → False
  rw [eq_iff_iff]
  decide

theorem holds_atMost_iff {s : Negation.Strength} :
    atMost.licenser.Holds s.toProjectivitySignature ↔ s ≤ .weak := by
  refine holds_toProjectivitySignature_iff (fun p ↦ ProjectivitySignature.holdsFor_anti_iff.mpr
    (scopeAntitone_atMost p.n p.A)) fun s hs h ↦ ?_
  have := (ProjectivitySignature.holdsFor_antiAdd_iff.mp
    ((h.toProjectivitySignature_of_le (s := .antiAdditive)
    (by revert hs; cases s <;> decide)) ⟨⟨⟨Bool, Set.univ⟩⟩, 1⟩)).1 {true} {false}
  revert this
  show Det.atMost 1 (Set.univ : Set Bool) ({true} ∪ {false}) = (_ ∧ _) → False
  rw [eq_iff_iff]
  decide

/-- The restrictor of a universal is the scope of a universal over the complement of its scope,
applied after negation. -/
theorem holds_universalRestrictor_iff {s : Negation.Strength} :
    universalRestrictor.licenser.Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive :=
  Negation.Strength.forall_holdsFor_iff_le_antiAdditive
    (g := fun p : NonuniversalPredicate ↦ Det.every p.Aᶜ)
    (fun _ ↦ funext fun _ ↦ propext Set.compl_subset_compl.symm)
    (fun p ↦ holdsFor_mult_every (Set.nonempty_compl.2 fun h ↦ p.nonuniversal.elim
      fun x hx ↦ hx (h ▸ Set.mem_univ x)))
    ⟨⟨⟨Bool, ∅⟩, ⟨true, Set.notMem_empty true⟩⟩, not_holdsFor_additive_every (a := true)
      (b := false) (Set.notMem_empty _) (Set.notMem_empty _) (by decide)⟩

/-- Since *no* is symmetric, the restrictor of *no* is the scope of a universal over the scope,
applied after negation. -/
theorem holds_noRestrictor_iff {s : Negation.Strength} :
    noRestrictor.licenser.Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive :=
  Negation.Strength.forall_holdsFor_iff_le_antiAdditive (g := fun p : NonemptyPredicate ↦
    Det.every p.A) (fun _ ↦ funext fun _ ↦ propext Set.subset_compl_comm)
    (fun p ↦ holdsFor_mult_every p.nonempty)
    ⟨⟨⟨Bool, .univ⟩, Set.univ_nonempty⟩, not_holdsFor_additive_every (a := true) (b := false)
      trivial trivial (by decide)⟩

theorem holds_withoutClause_iff {s : Negation.Strength} :
    withoutClause.licenser.Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive :=
  Negation.Strength.forall_holdsFor_iff_le_antiAdditive (g := fun p : Predicate ↦ (p.A ⊓ ·))
    (fun _ ↦ funext fun _ ↦ sdiff_eq) (fun p ↦ holdsFor_mult_inf_left p.A)
    ⟨⟨Unit, ∅⟩, fun h ↦ Set.empty_ne_univ
      ((ProjectivitySignature.holdsFor_additive_iff.1 h).2.symm.trans (Set.empty_inter _)).symm⟩

theorem holds_beforeClause_iff {s : Negation.Strength} :
    beforeClause.licenser.Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive := by
  refine holds_toProjectivitySignature_iff (fun p ↦ ProjectivitySignature.holdsFor_antiAdd_iff.mpr
    ⟨isAntiAdditive_beforeEver p.A, eq_bot_iff.2 not_beforeEver_top⟩)
    fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (ProjectivitySignature.holdsFor_antiAddMult_iff.mp (h ⟨ℕ, ⊥⟩)).2.2
  simp [beforeEver] at this

/-- The operator placing the compared individual above the degrees of a clause is the scope of a
universal over the degrees from the degree of the individual upward, applied after negation. -/
theorem holds_exceedsFamily_iff {s : Negation.Strength} :
    (classical exceedsFamily).Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive :=
  Negation.Strength.forall_holdsFor_iff_le_antiAdditive
    (g := fun p : Measured ↦ Det.every (Set.Ici (p.μ p.x)))
    (fun _ ↦ funext fun _ ↦ propext ⟨fun h _ hd hd' ↦ (h hd').not_ge hd,
      fun h _ hd ↦ not_le.1 fun hd' ↦ h hd' hd⟩)
    (fun _ ↦ holdsFor_mult_every Set.nonempty_Ici)
    ⟨⟨ℕ, ℕ, id, 0⟩, not_holdsFor_additive_every (a := 0) (b := 1) (Set.mem_Ici.2 le_rfl)
      (Set.mem_Ici.2 zero_le_one) zero_ne_one⟩

theorem holds_clausalComparative_iff {s : Negation.Strength} :
    clausalComparative.licenser.Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive :=
  holds_exceedsFamily_iff

theorem holds_tooTo_iff {s : Negation.Strength} :
    tooTo.licenser.Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive :=
  holds_exceedsFamily_iff

theorem holds_doubtVerb_iff {s : Negation.Strength} :
    doubtVerb.licenser.Holds s.toProjectivitySignature ↔ s ≤ .weak :=
  Negation.Strength.forall_holdsFor_iff_le_weak
    (g := fun p : Accessibility ↦ fun P ↦ p.w ∈ p.R.core P) (fun _ ↦ rfl)
    (fun _ ↦ holdsFor_mono_mem_core) ⟨⟨Bool, .univ, true⟩, not_holdsFor_additive_mem_core⟩

theorem holds_denyVerb_iff {s : Negation.Strength} :
    denyVerb.licenser.Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive :=
  Negation.Strength.forall_holdsFor_iff_le_antiAdditive
    (g := fun p : SerialAccessibility ↦ fun P ↦ p.w ∈ p.R.core P) (fun _ ↦ rfl)
    (fun p ↦ holdsFor_mult_mem_core p.serial)
    ⟨⟨⟨Bool, .univ, true⟩, ⟨true, trivial⟩⟩, not_holdsFor_additive_mem_core⟩

/-- Negation over a neg-raising attitude is anti-additive. It is not anti-morphic, since it is
false of every complement where the modal base is empty. -/
theorem holds_superordinateNegation_iff {s : Negation.Strength} :
    superordinateNegation.licenser.Holds s.toProjectivitySignature ↔ s ≤ .antiAdditive :=
  holds_toProjectivitySignature_iff
    (fun p ↦ ProjectivitySignature.holdsFor_antiAdd_iff.2
      ⟨NegRaising.isAntiAdditive_posExt_negation p.R p.H,
        NegRaising.posExt_negation_univ p.R p.H⟩)
    fun s hs h ↦ by
      obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
      have := (ProjectivitySignature.holdsFor_antiAddMult_iff.1 (h ⟨Unit, ∅, ∅⟩)).2.2
      simpa [NegRaising.posExt_negation] using congrArg (() ∈ ·) this

/-! ### Non-triviality

Each downward entailing licenser has an operator that is not upward entailing. It is therefore not
downward entailing merely by being constant. -/

theorem not_isStrawsonUE_negation : ¬ negation.licenser.IsStrawsonUE :=
  not_forall.2 ⟨Unit, fun h ↦ h (bot_le (a := ⊤)) () id trivial⟩

theorem not_isStrawsonUE_nobody : ¬ nobody.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨⟨Unit, Set.univ⟩, Set.univ_nonempty⟩,
    fun h ↦ h (bot_le (a := ⊤)) (fun _ _ hx ↦ hx) (Set.mem_univ ()) trivial⟩

theorem not_isStrawsonUE_few : ¬ few.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨⟨Unit, Set.univ⟩⟩, fun h ↦ absurd
    (h (a := ∅) (b := Set.univ) (Set.empty_subset _) (by decide)) (by decide)⟩

theorem not_isStrawsonUE_atMost : ¬ atMost.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨⟨⟨Unit, Set.univ⟩⟩, 0⟩, fun h ↦ absurd
    (h (a := ∅) (b := Set.univ) (Set.empty_subset _) (by decide)) (by decide)⟩

theorem not_isStrawsonUE_universalRestrictor : ¬ universalRestrictor.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨⟨Unit, ∅⟩, ⟨(), Set.notMem_empty ()⟩⟩,
    fun h ↦ h (bot_le (a := ⊤)) (fun _ hx ↦ hx) (Set.mem_univ ())⟩

theorem not_isStrawsonUE_noRestrictor : ¬ noRestrictor.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨⟨Unit, Set.univ⟩, Set.univ_nonempty⟩,
    fun h ↦ h (bot_le (a := ⊤)) (Set.empty_subset _) (Set.mem_univ ()) (Set.mem_univ ())⟩

theorem not_isStrawsonUE_withoutClause : ¬ withoutClause.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Unit, Set.univ⟩, fun h ↦
    (h (bot_le (a := ⊤)) (Set.mem_sdiff_of_mem (Set.mem_univ ()) (Set.notMem_empty ()))).2 trivial⟩

theorem not_isStrawsonUE_beforeClause : ¬ beforeClause.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨ℕ, (· = NonemptyInterval.pure 0)⟩, fun h ↦
    let ⟨t, _, ht⟩ := h (bot_le (a := ⊤))
      ⟨0, ⟨_, rfl, by simp⟩, fun _ ⟨_, hi, _⟩ ↦ hi.elim⟩
    lt_irrefl t (ht t ⟨NonemptyInterval.pure t, trivial, by simp⟩)⟩

theorem not_isStrawsonUE_exceedsFamily : ¬ (Licenser.classical exceedsFamily).IsStrawsonUE :=
  not_forall.2 ⟨⟨ℕ, ℕ, id, 1⟩, fun h ↦
    lt_irrefl _ (h (bot_le (a := ⊤)) (fun _ hd ↦ hd.elim) (Set.mem_univ 1))⟩

theorem not_isStrawsonUE_doubtVerb : ¬ doubtVerb.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Bool, .univ, true⟩, fun h ↦ h (bot_le (a := ⊤))
    (fun hc ↦ Set.notMem_empty _ (hc (Set.mem_univ (true, true)))) fun _ _ ↦ trivial⟩

theorem not_isStrawsonUE_denyVerb : ¬ denyVerb.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨⟨Bool, .univ, true⟩, ⟨true, trivial⟩⟩, fun h ↦
    h (bot_le (a := ⊤)) (fun _ _ ↦ Set.notMem_empty _) (Set.mem_univ (true, true))
      (Set.mem_univ true)⟩

theorem not_isStrawsonUE_superordinateNegation :
    ¬ superordinateNegation.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Unit, .univ, .univ⟩, Presupposition.not_isStrawsonUE (w := ())
    (Set.empty_subset Set.univ)
    (by simp [NegRaising.negation, NegRaising.box_eq_false_iff, ModalLogic.Box])
    (by simp [NegRaising.negation, NegRaising.box, ModalLogic.Box])⟩

theorem not_isStrawsonUE_onlyFocus : ¬ onlyFocus.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Bool, Unit, true⟩, Focus.not_isStrawsonUE_only_eq⟩

theorem not_isStrawsonUE_adversative : ¬ adversative.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Fin 3, fun _ ↦ {0}, fun _ ↦ .univ, fun _ ↦ {{1}}⟩,
    Desire.BestWorlds.not_isStrawsonUE_regret⟩

theorem not_isStrawsonUE_superlative : ¬ superlative.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Bool, Unit, ℕ, fun _ ↦ 0, true⟩, not_isStrawsonUE_trivalentSuperlative⟩

theorem not_isStrawsonUE_conditionalAntecedent : ¬ conditionalAntecedent.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Unit, Bool, fun _ ↦ .univ, {true}⟩,
    Conditional.not_isStrawsonUE_horizonCounterfactual⟩

theorem not_isStrawsonUE_sinceTemporal : ¬ sinceTemporal.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨ℤ, (· - 5)⟩, not_isStrawsonUE_since⟩

/-! ### Scalar licensers

Once *few* and *at most n* are exhaustified against their stronger scale-mates, they assert
*some*, and so they are not downward entailing ([gajewski-2011]'s (45), (48)). -/

theorem not_holds_exhaustified_few : ¬ few.licenser.exhaustified.Holds .anti := fun h ↦ by
  have hA : ¬ Det.few (Set.univ : Set (Fin 3)) ≤ Det.no Set.univ := fun hle ↦
    absurd (hle {0} (by decide)) (by decide)
  have hanti : Antitone (Det.exhaustified Det.few {Det.no} (Set.univ : Set (Fin 3))) :=
    ProjectivitySignature.holdsFor_anti_iff.mp (h ⟨⟨Fin 3, Set.univ⟩⟩)
  refine Det.not_exhaustified_of_not_le (Set.mem_singleton _) (fun _ _ hx ↦ hx) hA
    (hanti (a := ∅) (b := {0}) (Set.empty_subset _) (Det.exhaustified_iff.2 ⟨by decide, ?_⟩))
  rintro _ rfl hno
  exact absurd hno (by decide)

theorem not_holds_exhaustified_atMost : ¬ atMost.licenser.exhaustified.Holds .anti := fun h ↦ by
  have hA : ¬ Det.atMost 1 (Set.univ : Set Bool) ≤ Det.atMost 0 Set.univ := fun hle ↦
    absurd (hle {true} (by decide)) (by decide)
  have hanti : Antitone (Det.exhaustified (Det.atMost 1) {Det.atMost 0} (Set.univ : Set Bool)) :=
    ProjectivitySignature.holdsFor_anti_iff.mp (h ⟨⟨⟨Bool, Set.univ⟩⟩, 1⟩)
  refine Det.not_exhaustified_of_not_le (Set.mem_singleton _)
    (show Det.atMost 0 (Set.univ : Set Bool) ∅ by decide) hA
    (hanti (a := ∅) (b := {true}) (Set.empty_subset _) (Det.exhaustified_iff.2 ⟨by decide, ?_⟩))
  rintro _ rfl hle
  exact absurd hle (by decide)

/-! ### Strawson licensers -/

theorem isStrawsonDE_onlyFocus : onlyFocus.licenser.IsStrawsonDE := fun p ↦
  Focus.isStrawsonDE_only_eq p.x

theorem not_holds_onlyFocus : ¬ onlyFocus.licenser.Holds .anti := fun h ↦
  Focus.not_antitone_posExt_only_eq
    (ProjectivitySignature.holdsFor_anti_iff.mp (h ⟨Bool, Unit, true⟩))

theorem isStrawsonDE_adversative : adversative.licenser.IsStrawsonDE := fun p ↦
  Desire.BestWorlds.isStrawsonDE_regret p.dox p.base p.g

theorem not_holds_adversative : ¬ adversative.licenser.Holds .anti := fun h ↦
  Desire.BestWorlds.not_antitone_posExt_regret (ProjectivitySignature.holdsFor_anti_iff.mp
    (h ⟨Bool, fun _ ↦ {true}, fun _ ↦ .univ, fun _ ↦ {{false}}⟩))

theorem isStrawsonDE_superlative : superlative.licenser.IsStrawsonDE := fun p ↦
  isStrawsonDE_trivalentSuperlative p.μ p.x

theorem not_holds_superlative : ¬ superlative.licenser.Holds .anti := fun h ↦
  not_antitone_posExt_trivalentSuperlative (ProjectivitySignature.holdsFor_anti_iff.mp
    (h ⟨Unit, Unit, ℕ, fun _ ↦ 0, ()⟩))

theorem isStrawsonDE_conditionalAntecedent : conditionalAntecedent.licenser.IsStrawsonDE :=
  fun p ↦ Conditional.isStrawsonDE_horizonCounterfactual p.horizon p.q

theorem not_holds_conditionalAntecedent : ¬ conditionalAntecedent.licenser.Holds .anti := fun h ↦
  Conditional.not_antitone_posExt_horizonCounterfactual
    (ProjectivitySignature.holdsFor_anti_iff.mp
    (h ⟨Unit, Unit, fun _ ↦ .univ, .univ⟩))

theorem isStrawsonDE_sinceTemporal : sinceTemporal.licenser.IsStrawsonDE := fun p ↦
  isStrawsonDE_since p.ago

theorem not_holds_sinceTemporal : ¬ sinceTemporal.licenser.Holds .anti := fun h ↦
  not_antitone_posExt_since (ProjectivitySignature.holdsFor_anti_iff.mp (h ⟨ℤ, (· - 5)⟩))

/-! ### Modal licensers and questions -/

/-- A frame over three worlds in which the first world accesses the other two, and each of the
other two is the one world at which one of two individuals is a witness. -/
private def branching : SetRel (Fin 3) (Fin 3) := {p | p.1 = 0 ∧ p.2 ≠ 0}

private def witnessAt (d : Fin 2) : Set (Fin 3) := {d.succ}

theorem licensesFreeChoice_necessityFamily : (Licenser.modal necessityFamily).LicensesFreeChoice :=
  ⟨⟨Fin 3, branching⟩, Fin 2, witnessAt, .univ, by decide, 0,
    Exhaustification.mem_antiExh_iff.2 ⟨fun v hv ↦
      let ⟨d, hd⟩ := Fin.exists_succ_eq.2 hv.2; Set.mem_iUnion₂.2 ⟨d, Finset.mem_univ _, hd.symm⟩,
      .inr fun S hS _ h ↦
        let ⟨c, _, hc⟩ := Finset.exists_of_ssubset hS
        let ⟨_, he, hec⟩ := Set.mem_iUnion₂.1 (@h c.succ ⟨rfl, c.succ_ne_zero⟩)
        hc (Fin.succ_injective _ hec ▸ he)⟩⟩

theorem licensesFreeChoice_modalPossibility : modalPossibility.licenser.LicensesFreeChoice :=
  ⟨⟨Fin 3, branching⟩, Fin 2, witnessAt, .univ, by decide, 0, by
    show 0 ∈ Exhaustification.antiExh
      (fun S ↦ branching.preimage (⋃ d ∈ S, witnessAt d)) .univ
    rw [Exhaustification.antiExh_preimage_biUnion witnessAt branching Finset.univ_nonempty]
    exact Set.mem_iInter₂.2 fun d _ ↦ ⟨d.succ, rfl, rfl, d.succ_ne_zero⟩⟩

/-- Necessity is upward entailing. -/
theorem isStrawsonUE_necessityFamily : (Licenser.modal necessityFamily).IsStrawsonUE :=
  fun _ ↦ SetRel.core_mono

/-- Possibility is upward entailing. -/
theorem isStrawsonUE_modalPossibility : modalPossibility.licenser.IsStrawsonUE :=
  fun _ ↦ SetRel.preimage_mono

/-- Necessity is not downward entailing, since it is the identity at a world that accesses
itself. -/
theorem not_holds_anti_necessityFamily : ¬ (Licenser.modal necessityFamily).Holds .anti :=
  fun h ↦ by
    have := ProjectivitySignature.holdsFor_anti_iff.1 (h ⟨Unit, .univ⟩) (Set.empty_subset .univ)
    simp [Set.subset_def, SetRel.core] at this

/-- Possibility is not downward entailing, since it is the identity at a world that accesses
itself. -/
theorem not_holds_anti_modalPossibility : ¬ modalPossibility.licenser.Holds .anti :=
  fun h ↦ by
    have := ProjectivitySignature.holdsFor_anti_iff.1 (h ⟨Unit, .univ⟩) (Set.empty_subset .univ)
    simp [Set.subset_def, SetRel.preimage] at this

/-- The identity is not downward entailing. -/
theorem not_holds_anti_positiveAssertion : ¬ positiveAssertion.licenser.Holds .anti := fun h ↦
  ProjectivitySignature.holdsFor_anti_iff.1 (h Unit) (bot_le (a := ⊤)) () trivial

/-! ### The profiles of the contexts

The profile of a context is a table. It is the profile of the licenser of the context, so a claim
about what a context licenses is decided on the table and rests on the theorems above. A question
has no profile. -/

/-- What the strengths of negation say of a construction: the greatest strength it carries, the
greatest strength it holds outright, and whether it licenses free choice. A question has no
profile. -/
def profile : LicensingContext → Option Profile
  | negation => some ⟨ofStrength .antiMorphic, ofStrength .antiMorphic, false⟩
  | nobody | universalRestrictor | noRestrictor | withoutClause | beforeClause
  | clausalComparative | tooTo | denyVerb | superordinateNegation =>
    some ⟨ofStrength .antiAdditive, ofStrength .antiAdditive, false⟩
  | few | atMost | doubtVerb => some ⟨ofStrength .weak, ofStrength .weak, false⟩
  | onlyFocus | adversative | superlative | conditionalAntecedent | sinceTemporal =>
    some ⟨ofStrength .weak, ⊥, false⟩
  | modalPossibility | modalNecessity | imperative | generic | freeRelative => some ⟨⊥, ⊥, true⟩
  | positiveAssertion => some ⟨⊥, ⊥, false⟩
  | polarQuestion | constituentQuestion => none

private theorem profile_eq_of {L : Licenser} {a b : WithBot (WithTop Negation.Strength)}
    {fc : Bool} (hc : L.carried = a) (hh : L.held = b) (hf : L.LicensesFreeChoice ↔ fc = true) :
    some (⟨a, b, fc⟩ : Profile) = some L.profile :=
  congrArg some (Licenser.profile_eq_mk hc hh hf).symm

private theorem carried_of_holds_iff {F : Licenser.OperatorFamily} {s₀ : Negation.Strength}
    (hn : ¬ (classical F).IsStrawsonUE)
    (h : ∀ {s : Negation.Strength}, (classical F).Holds s.toProjectivitySignature ↔ s ≤ s₀) :
    (classical F).carried = ofStrength s₀ :=
  carried_eq_coe fun _ ↦ carries_classical_iff_le hn fun _ ↦ h

private theorem carried_of_eq_weak {L : Licenser} (hde : L.IsStrawsonDE) (hn : ¬ L.IsStrawsonUE)
    (h : ¬ L.exhaustified.Holds .anti) : L.carried = ofStrength .weak :=
  carried_eq_coe fun _ ↦ (carries_iff_eq_weak hde hn h).trans Negation.Strength.le_weak_iff.symm

private theorem held_strawson_eq_bot {L : Licenser} (h : ¬ L.Holds .anti) : L.held = ⊥ :=
  held_eq_bot fun _ ↦ not_holds_toProjectivitySignature h

private theorem not_fc {b : Prop} (h : ¬ b) : b ↔ false = true := iff_of_false h Bool.false_ne_true

/-- The profile of a context is the profile of its licenser. -/
theorem profile_eq :
    ∀ (c : LicensingContext) (h : c.HasLicenser), c.profile = some (c.licenser h).profile
  | negation, _ => profile_eq_of
      (carried_eq_coe fun s ↦ ⟨fun _ ↦ s.le_antiMorphic, fun _ ↦
        carries_classical_iff.2 ⟨holds_negation _, not_isStrawsonUE_negation⟩⟩)
      (held_eq_coe fun s ↦ ⟨fun _ ↦ s.le_antiMorphic, fun _ ↦ holds_negation s⟩) (not_fc id)
  | nobody, _ => profile_eq_of (carried_of_holds_iff not_isStrawsonUE_nobody holds_nobody_iff)
      (held_eq_coe fun _ ↦ holds_nobody_iff) (not_fc id)
  | universalRestrictor, _ => profile_eq_of
      (carried_of_holds_iff not_isStrawsonUE_universalRestrictor holds_universalRestrictor_iff)
      (held_eq_coe fun _ ↦ holds_universalRestrictor_iff) (not_fc id)
  | noRestrictor, _ => profile_eq_of
      (carried_of_holds_iff not_isStrawsonUE_noRestrictor holds_noRestrictor_iff)
      (held_eq_coe fun _ ↦ holds_noRestrictor_iff) (not_fc id)
  | withoutClause, _ => profile_eq_of
      (carried_of_holds_iff not_isStrawsonUE_withoutClause holds_withoutClause_iff)
      (held_eq_coe fun _ ↦ holds_withoutClause_iff) (not_fc id)
  | beforeClause, _ => profile_eq_of
      (carried_of_holds_iff not_isStrawsonUE_beforeClause holds_beforeClause_iff)
      (held_eq_coe fun _ ↦ holds_beforeClause_iff) (not_fc id)
  | clausalComparative, _ | tooTo, _ => profile_eq_of
      (carried_of_holds_iff not_isStrawsonUE_exceedsFamily holds_exceedsFamily_iff)
      (held_eq_coe fun _ ↦ holds_exceedsFamily_iff) (not_fc id)
  | denyVerb, _ => profile_eq_of
      (carried_of_holds_iff not_isStrawsonUE_denyVerb holds_denyVerb_iff)
      (held_eq_coe fun _ ↦ holds_denyVerb_iff) (not_fc id)
  | superordinateNegation, _ => profile_eq_of
      (carried_eq_coe fun _ ↦ carries_iff_le
        (isStrawsonDE_of_holds_anti (holds_superordinateNegation_iff.2 bot_le))
        not_isStrawsonUE_superordinateNegation fun _ ↦ holds_superordinateNegation_iff)
      (held_eq_coe fun _ ↦ holds_superordinateNegation_iff) (not_fc id)
  | few, _ => profile_eq_of
      (carried_of_eq_weak (isStrawsonDE_of_holds_anti (holds_few_iff.2 le_rfl))
        not_isStrawsonUE_few not_holds_exhaustified_few)
      (held_eq_coe fun _ ↦ holds_few_iff) (not_fc id)
  | atMost, _ => profile_eq_of
      (carried_of_eq_weak (isStrawsonDE_of_holds_anti (holds_atMost_iff.2 le_rfl))
        not_isStrawsonUE_atMost not_holds_exhaustified_atMost)
      (held_eq_coe fun _ ↦ holds_atMost_iff) (not_fc id)
  | doubtVerb, _ => profile_eq_of
      (carried_of_holds_iff not_isStrawsonUE_doubtVerb holds_doubtVerb_iff)
      (held_eq_coe fun _ ↦ holds_doubtVerb_iff) (not_fc id)
  | onlyFocus, _ => profile_eq_of
      (carried_of_eq_weak isStrawsonDE_onlyFocus not_isStrawsonUE_onlyFocus not_holds_onlyFocus)
      (held_strawson_eq_bot not_holds_onlyFocus) (not_fc id)
  | adversative, _ => profile_eq_of
      (carried_of_eq_weak isStrawsonDE_adversative not_isStrawsonUE_adversative
        not_holds_adversative)
      (held_strawson_eq_bot not_holds_adversative) (not_fc id)
  | superlative, _ => profile_eq_of
      (carried_of_eq_weak isStrawsonDE_superlative not_isStrawsonUE_superlative
        not_holds_superlative)
      (held_strawson_eq_bot not_holds_superlative) (not_fc id)
  | conditionalAntecedent, _ => profile_eq_of
      (carried_of_eq_weak isStrawsonDE_conditionalAntecedent
        not_isStrawsonUE_conditionalAntecedent not_holds_conditionalAntecedent)
      (held_strawson_eq_bot not_holds_conditionalAntecedent) (not_fc id)
  | sinceTemporal, _ => profile_eq_of
      (carried_of_eq_weak isStrawsonDE_sinceTemporal not_isStrawsonUE_sinceTemporal
        not_holds_sinceTemporal)
      (held_strawson_eq_bot not_holds_sinceTemporal) (not_fc id)
  | modalPossibility, _ => profile_eq_of
      (carried_eq_bot fun _ h ↦ h.weak.2 isStrawsonUE_modalPossibility)
      (held_strawson_eq_bot not_holds_anti_modalPossibility)
      (iff_of_true licensesFreeChoice_modalPossibility rfl)
  | modalNecessity, _ | imperative, _ | generic, _ | freeRelative, _ => profile_eq_of
      (carried_eq_bot fun _ h ↦ h.weak.2 isStrawsonUE_necessityFamily)
      (held_strawson_eq_bot not_holds_anti_necessityFamily)
      (iff_of_true licensesFreeChoice_necessityFamily rfl)
  | positiveAssertion, _ => profile_eq_of
      (carried_eq_bot fun _ h ↦ h.weak.2 fun _ ↦ monotone_id)
      (held_strawson_eq_bot not_holds_anti_positiveAssertion) (not_fc id)

/-! ### Licensing at the named contexts -/

variable (c : LicensingContext) (k : Class)

/-- A context **licenses** a class when it has a profile that licenses the class. -/
def Licenses : Prop := ∃ p ∈ c.profile, p.Licenses k

/-- A context **anti-licenses** a class when it has a profile that anti-licenses the class. -/
def AntiLicenses : Prop := ∃ p ∈ c.profile, p.AntiLicenses k

/-- A context **admits** a class when it has a profile that admits the class. -/
def Admits : Prop := ∃ p ∈ c.profile, p.Admits k

instance : Decidable (c.Licenses k) := inferInstanceAs (Decidable (∃ p ∈ _, _))

instance : Decidable (c.AntiLicenses k) := inferInstanceAs (Decidable (∃ p ∈ _, _))

instance : Decidable (c.Admits k) := inferInstanceAs (Decidable (∃ p ∈ _, _))

variable {c k}

theorem licenses_iff (h : c.HasLicenser) : c.Licenses k ↔ (c.licenser h).Licenses k := by
  simp [Licenses, profile_eq c h, Licenser.profile_licenses_iff]

theorem antiLicenses_iff (h : c.HasLicenser) :
    c.AntiLicenses k ↔ (c.licenser h).AntiLicenses k := by
  simp [AntiLicenses, profile_eq c h, Licenser.profile_antiLicenses_iff]

theorem admits_iff (h : c.HasLicenser) : c.Admits k ↔ (c.licenser h).Admits k := by
  simp [Admits, profile_eq c h, Licenser.profile_admits_iff]

/-- A context licenses a class of negative polarity items that are not free choice items exactly
when its licenser carries the strength that the class requires. -/
theorem licenses_npi_iff (h : c.HasLicenser) {s : Negation.Strength} :
    c.Licenses (.npi s) ↔ (c.licenser h).Carries s :=
  (licenses_iff h).trans (Licenser.licenses_npi_iff.trans (or_iff_left (by simp)))

/-- A question licenses no class. -/
theorem not_licenses_of_not_hasLicenser (h : ¬ c.HasLicenser) : ¬ c.Licenses k := by
  cases c <;> first | exact absurd trivial h | simp [Licenses, profile]

/-- The contexts that the strengths of negation rank: all but the questions. -/
def ranked : Finset LicensingContext := Finset.univ.filter HasLicenser

end LicensingContext

/-! ### The classes with which an entry is compatible -/

/-- The contexts in which the strengths of negation predict a class to be possible: those whose
profile admits the class. A question has no profile and lies in no region. -/
def Class.region (k : Class) : Finset LicensingContext := Finset.univ.filter (·.Admits k)

/-- An entry and a class are **compatible** when the region of the class contains every ranked
context in which the sources attest the item and no context from which they exclude it. The two
agree wherever both say something: an entry on which the sources are silent is compatible with
every class, and an entry may be compatible with several classes or with none. -/
def Compatible (e : PolarityItem) (k : Class) : Prop :=
  e.attested ∩ LicensingContext.ranked ⊆ k.region ∧ Disjoint e.excluded k.region

instance (e : PolarityItem) (k : Class) : Decidable (e.Compatible k) :=
  inferInstanceAs (Decidable (_ ∧ _))

end PolarityItem
