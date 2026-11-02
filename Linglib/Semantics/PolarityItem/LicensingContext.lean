/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.PolarityItem.Licenser
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Quantification.Signatures
public import Linglib.Semantics.Reference.Indefinite
public import Linglib.Semantics.Tense.RunTimes
public import Mathlib.Basic.Rel

/-!
# Licensing contexts

A licensing context is a construction that can host a polarity item. It places a licenser over the
item and realizes a function of Haspelmath's implicational map, where it realizes one, and what its
licenser carries is a theorem about the operators it denotes. Clausal negation is anti-morphic.
*Nobody*, the restrictor of a universal, *without*, *deny*, *before*, *too … to* and the clausal
comparative are anti-additive and no more, and *doubt* downward entailing and no more. *Few* and *at
most* are scalar: downward entailing, and not even that once exhaustified against the stronger *no*
and *at most n − 1*, the determiner exhaustification `Quantifier.Det.exhaustified`. Every downward
entailing context is so non-trivially. Focus *only*, adversatives, superlatives, conditional
antecedents and temporal *since* are downward entailing only modulo their presuppositions, the
modals, imperatives, generics and free relatives are modal licensers, and questions license by
relevance. A study can state the theory of a licenser of its own; the named constructions are the
shared inventory that lexical entries cite.

## Main declarations

* `PolarityItem.LicensingContext`: the named constructions.
* `PolarityItem.LicensingContext.licenser`, `PolarityItem.LicensingContext.haspelmath`: the
  operator a construction places over the item and its function on Haspelmath's map.
* `Quantifier.Det.exhaustified`: a determiner exhaustified against its scale-mates.
* `PolarityItem.LicensingContext.holds_negation`, `holds_nobody_iff`, `not_isStrawsonUE_nobody`,
  `not_holds_exhaustified_few`, …: the certificates of each context's licenser.

## Implementation notes

* A context is a name, so the lexical entries that list the contexts an item is attested in are
  computable data with decidable equality, while the licenser, often defined classically, is a
  function of the name. Distinct constructions can share a licenser: the necessity modal, the
  imperative, the generic and the free relative are all necessities, and the clausal comparative
  and *too … to* both exceed the clause's degrees.
* The inventory is the contexts the library gives a semantics, not an exhaustive list. It realizes
  six of Haspelmath's nine functions; the irrealis non-specific function, where nonveridical rather
  than downward-entailing operators license, has no context yet, and neither do many licensers of
  the downward-entailing literature, such as negative adverbs, *neither … nor*, the restrictor of
  *no* or *not every*.
* *Before* is Anscombe's universal reading, *before ever*. *Too … to* is the
  subject's degree exceeding every degree at which the infinitive holds, after Meier. *Doubt* is not
  believing and *deny* asserting the negation, over a doxastic or assertoric accessibility.
* The free relative is read as a necessity over its alternatives, with the modal presupposition of
  *-ever*; the generic is a necessity over normal worlds.
* Haspelmath's placements are his book's. *Nobody*, *before*-clauses and adversatives sit between
  direct and indirect negation there, so they realize no function here, nor do the rows outside
  the map's inventory.

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
* [van-rooy-2003-npi]
* [haspelmath-1997]
-/

@[expose] public section

/-! ### Determiners exhaustified against their scale-mates -/

namespace Quantifier.Det

variable {α : Type*} {Q Q' : Det α} {C : Set (Det α)} {A P : Set α}

/-- The determiner `Q` exhaustified against its scale-mates `C` holds, at each restrictor, of the
scopes where `Q` holds and every scale-mate holding there is entailed, entailment holding the
restrictor fixed and quantifying over scopes ([gajewski-2011]'s `O` with `ALT-1`). -/
def exhaustified (Q : Det α) (C : Set (Det α)) : Det α :=
  fun A ↦ Exhaustification.exh ((· A) '' C) (Q A)

theorem exhaustified_iff : exhaustified Q C A P ↔ Q A P ∧ ∀ Q' ∈ C, Q' A P → Q A ≤ Q' A :=
  ⟨fun ⟨h, h'⟩ ↦ ⟨h, fun Q' hQ' hP ↦ h' _ ⟨Q', hQ', rfl⟩ hP⟩,
    fun ⟨h, h'⟩ ↦ ⟨h, by rintro _ ⟨Q', hQ', rfl⟩ hP; exact h' Q' hQ' hP⟩⟩

theorem not_exhaustified_of_not_le (hQ' : Q' ∈ C) (hP : Q' A P) (h : ¬ Q A ≤ Q' A) :
    ¬ exhaustified Q C A P :=
  fun he ↦ h ((exhaustified_iff.1 he).2 Q' hQ' hP)

theorem exhaustified_eq_of_forall_le (h : ∀ Q' ∈ C, ∀ P, Q' A P → Q A ≤ Q' A) :
    exhaustified Q C A = Q A :=
  Exhaustification.exh_eq_self_iff.2 (by rintro _ ⟨Q', hQ', rfl⟩ ⟨P, _, hP⟩; exact h Q' hQ' P hP)

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

/-- A licensing context is a construction that can host a polarity item. What it does to the item
is the licenser it places over the item's position (`LicensingContext.licenser`), and where it sits
typologically is the function of [haspelmath-1997]'s implicational map it realizes
(`LicensingContext.haspelmath`). Distinct constructions can share a licenser, as the necessity
modal, the imperative, the generic and the free relative do. -/
inductive LicensingContext where
  /-- Clausal negation, as in *not*, complement over predicates. -/
  | negation
  /-- A negative quantifier, as in *nobody*, over a restrictor true of something. -/
  | nobody
  /-- *Few* NP, the proportional reading of the English fragment, below the stronger *no* on its
  scale. -/
  | few
  /-- *At most n* NP, below the stronger *at most n − 1* on its scale. -/
  | atMost
  /-- The restrictor of a universal, as in *everyone who*, over a scope false of something. -/
  | universalRestrictor
  /-- A *without*-phrase, the matrix predicate holding without the phrase's. -/
  | withoutClause
  /-- A *before*-clause, Anscombe's universal *before*. -/
  | beforeClause
  /-- A clausal comparative, *taller than S*, the individual above every degree of the clause. -/
  | clausalComparative
  /-- *Too* ADJ *to* VP, the individual above every degree at which the infinitive holds. -/
  | tooTo
  /-- A verb of doubting, as in *I doubt that*, which does not believe its complement. -/
  | doubtVerb
  /-- A verb of denying, as in *she denied that*, which asserts the negation of its complement. -/
  | denyVerb
  /-- The scope of focus *only*, von Fintel's *only*. -/
  | onlyFocus
  /-- An adversative predicate, as in *sorry*, *surprised*, *regret*. -/
  | adversative
  /-- A superlative, in its comparison class. -/
  | superlative
  /-- The antecedent of a conditional, the modal-horizon counterfactual. -/
  | conditionalAntecedent
  /-- Temporal *since*, as in *it's been five years since*. -/
  | sinceTemporal
  /-- A question. -/
  | question
  /-- A possibility modal. -/
  | modalPossibility
  /-- A necessity modal. -/
  | modalNecessity
  /-- An imperative, a necessity over what is commanded. -/
  | imperative
  /-- A generic sentence, a necessity over normal worlds. -/
  | generic
  /-- A free relative, as in *whatever*, *whoever*, a necessity over its alternatives. -/
  | freeRelative
  deriving DecidableEq, Fintype, Repr

/-- The function of [haspelmath-1997]'s implicational map a construction realizes, if any. -/
def LicensingContext.haspelmath : LicensingContext → Option HaspelmathFunction
  | negation => some .directNeg
  | withoutClause | doubtVerb | denyVerb => some .indirectNeg
  | clausalComparative => some .comparative
  | conditionalAntecedent => some .conditional
  | question => some .question
  | modalPossibility | modalNecessity | imperative | generic | freeRelative => some .freeChoice
  | nobody | few | atMost | universalRestrictor | beforeClause | tooTo | onlyFocus | adversative
  | superlative | sinceTemporal => none

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

/-- A predicate true of something, the restrictor of a negative quantifier. -/
structure NonemptyPredicate extends Predicate where
  nonempty : A.Nonempty

/-- A predicate false of something, the scope of a universal. -/
structure NonuniversalPredicate extends Predicate where
  nonuniversal : ∃ x, x ∉ A

/-- A bound and a finite predicate, the restrictor of *at most n*. -/
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
  A : Set (NonemptyInterval T)

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

/-- The doxastic state, the domain and the ordering source of an adversative attitude. -/
structure Attitude where
  /-- The worlds. -/
  W : Type
  /-- The doxastic state. -/
  dox : W → Set W
  /-- The domain. -/
  base : W → Set W
  /-- The ordering source. -/
  g : W → Set (W → Prop)

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

namespace LicensingContext

/-! ### The licensers of the contexts -/

/-- The degrees a clause leaves the compared individual above. -/
abbrev exceedsFamily : OperatorFamily :=
  ⟨Measured, fun p ↦ Set p.D, fun _ ↦ Prop, fun p Δ ↦ p.μ p.x ∈ strictUpperBounds Δ⟩

/-- Necessity over a frame. -/
abbrev necessityFamily : ModalFamily := ⟨Frame, fun p ↦ p.W, fun p ↦ p.R.core⟩

/-- The licenser a construction places over the position of a polarity item. -/
noncomputable def licenser : LicensingContext → Licenser
  | negation => .classical ⟨Type, fun α ↦ α → Prop, fun α ↦ α → Prop, fun _ ↦ compl⟩
  | nobody => .classical ⟨NonemptyPredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p ↦ Det.no p.A⟩
  | few => .scalar ⟨⟨FinitePredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p ↦ Det.few p.A⟩,
      fun p ↦ Det.exhaustified Det.few {Det.no} p.A⟩
  | atMost => .scalar
      ⟨⟨BoundedPredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p ↦ Det.atMost p.n p.A⟩,
        fun p ↦ Det.exhaustified (Det.atMost p.n) {Det.atMost (p.n - 1)} p.A⟩
  | universalRestrictor => .classical
      ⟨NonuniversalPredicate, fun p ↦ Set p.ι, fun _ ↦ Prop, fun p R ↦ Det.every R p.A⟩
  | withoutClause => .classical
      ⟨Predicate, fun p ↦ Set p.ι, fun p ↦ Set p.ι, fun p V ↦ p.A \ V⟩
  | beforeClause => .classical
      ⟨MainClause, fun p ↦ Set (NonemptyInterval p.T), fun _ ↦ Prop, fun p ↦ beforeEver p.A⟩
  | clausalComparative | tooTo => .classical exceedsFamily
  | doubtVerb => .classical
      ⟨Accessibility, fun p ↦ Set p.W, fun _ ↦ Prop, fun p P ↦ p.w ∉ p.R.core P⟩
  | denyVerb => .classical
      ⟨SerialAccessibility, fun p ↦ Set p.W, fun _ ↦ Prop, fun p P ↦ p.w ∈ p.R.core Pᶜ⟩
  | onlyFocus => .strawson ⟨Focus, fun p ↦ p.ι → Set p.W, fun p ↦ p.W, fun p ↦ only p.x⟩
  | adversative => .strawson ⟨Attitude, fun p ↦ Set p.W, fun p ↦ p.W,
      fun p ↦ Desire.BestWorlds.regret p.dox p.base p.g⟩
  | superlative => .strawson ⟨Superlative, fun p ↦ p.W → Set p.α, fun p ↦ p.W,
      fun p C ↦ Degree.superlative p.μ C p.x⟩
  | conditionalAntecedent => .strawson ⟨Horizon, fun p ↦ Set p.W, fun p ↦ p.I,
      fun p P ↦ Conditional.horizonCounterfactual p.horizon P p.q⟩
  | sinceTemporal => .strawson ⟨Ago, fun p ↦ Set p.T, fun p ↦ p.T, fun p ↦ since p.ago⟩
  | question => .question
  | modalPossibility => .modal ⟨Frame, fun p ↦ p.W, fun p ↦ p.R.preimage⟩
  | modalNecessity | imperative | generic | freeRelative => .modal necessityFamily

/-! ### Classical licensers -/

open Licenser

theorem holds_negation (s : Negation.Strength) : negation.licenser.Holds s.toSignature :=
  (show negation.licenser.Holds .antiAddMult from fun _ ↦
    Signature.holdsFor_antiAddMult_compl).toSignature_of_le (s := s) (t := .antiMorphic) le_top

theorem holds_nobody_iff {s : Negation.Strength} :
    nobody.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨rightAntiAdditive_no _,
      eq_false fun h ↦ p.nonempty.elim fun _ hx ↦ h hx trivial⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨⟨Bool, Set.univ⟩, Set.univ_nonempty⟩)).2.1
    {true} {false}
  simp [Det.no] at this

theorem holds_few_iff {s : Negation.Strength} : few.licenser.Holds s.toSignature ↔ s ≤ .weak := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_anti_iff.mpr (scopeAntitone_few p.A))
    fun s hs h ↦ ?_
  have := (Signature.holdsFor_antiAdd_iff.mp ((h.toSignature_of_le (s := .antiAdditive)
    (by revert hs; cases s <;> decide)) ⟨⟨Fin 3, Set.univ⟩⟩)).1 {0} {1}
  revert this
  show Det.few (Set.univ : Set (Fin 3)) ({0} ∪ {1}) = (_ ∧ _) → False
  rw [eq_iff_iff]
  decide

theorem holds_atMost_iff {s : Negation.Strength} :
    atMost.licenser.Holds s.toSignature ↔ s ≤ .weak := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_anti_iff.mpr
    (scopeAntitone_atMost p.n p.A)) fun s hs h ↦ ?_
  have := (Signature.holdsFor_antiAdd_iff.mp ((h.toSignature_of_le (s := .antiAdditive)
    (by revert hs; cases s <;> decide)) ⟨⟨⟨Bool, Set.univ⟩⟩, 1⟩)).1 {true} {false}
  revert this
  show Det.atMost 1 (Set.univ : Set Bool) ({true} ∪ {false}) = (_ ∧ _) → False
  rw [eq_iff_iff]
  decide

theorem holds_universalRestrictor_iff {s : Negation.Strength} :
    universalRestrictor.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨leftAntiAdditive_every _,
      eq_false fun h ↦ p.nonuniversal.elim fun _ hx ↦ hx (h trivial)⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp
    (h ⟨⟨Bool, ∅⟩, ⟨true, Set.notMem_empty true⟩⟩)).2.1 {true} {false}
  simp [Det.every] at this

theorem holds_withoutClause_iff {s : Negation.Strength} :
    withoutClause.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨fun _ _ ↦ sdiff_sup, sdiff_top _⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨Unit, ∅⟩)).2.2
  exact Set.empty_ne_univ (by simpa using this)

theorem holds_beforeClause_iff {s : Negation.Strength} :
    beforeClause.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨fun _ _ ↦ propext beforeEver_union_right,
    eq_bot_iff.2 fun ⟨t, _, h⟩ ↦ lt_irrefl t (h t ⟨NonemptyInterval.pure t, trivial, by simp⟩)⟩)
    fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨ℕ, ∅⟩)).2.2
  simp [beforeEver, timeTrace] at this

theorem holds_exceedsFamily_iff {s : Negation.Strength} :
    (classical exceedsFamily).Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨fun Δ Δ' ↦ propext (show _ ∈ strictUpperBounds (Δ ∪ Δ') ↔ _ ∈ strictUpperBounds Δ ∧ _ by
      simp [strictUpperBounds, or_imp, forall_and]),
      eq_false fun h ↦ lt_irrefl _ (h (Set.mem_univ (p.μ p.x)))⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨ℕ, ℕ, id, 1⟩)).2.1 ({2} : Set ℕ) {1}
  simp at this

theorem holds_clausalComparative_iff {s : Negation.Strength} :
    clausalComparative.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive :=
  holds_exceedsFamily_iff

theorem holds_tooTo_iff {s : Negation.Strength} :
    tooTo.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive :=
  holds_exceedsFamily_iff

theorem holds_doubtVerb_iff {s : Negation.Strength} :
    doubtVerb.licenser.Holds s.toSignature ↔ s ≤ .weak := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_anti_iff.mpr
    fun P Q hPQ hQ hP ↦ hQ fun _ hv ↦ hPQ (hP hv)) fun s hs h ↦ ?_
  have := (Signature.holdsFor_antiAdd_iff.mp ((h.toSignature_of_le (s := .antiAdditive)
    (by revert hs; cases s <;> decide)) ⟨Bool, .univ, true⟩)).1 {true} {false}
  revert this
  simp only [SetRel.core, Set.mem_ofPred_eq, Set.sup_eq_union, inf_Prop_eq, eq_iff_iff]
  decide

theorem holds_denyVerb_iff {s : Negation.Strength} :
    denyVerb.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨fun P Q ↦ propext (show p.w ∈ p.R.core (P ∪ Q)ᶜ ↔ p.w ∈ p.R.core Pᶜ ∧ p.w ∈ p.R.core Qᶜ from
      ⟨fun h ↦ ⟨fun _ hv hP ↦ h hv (.inl hP), fun _ hv hQ ↦ h hv (.inr hQ)⟩,
        fun ⟨h₁, h₂⟩ _ hv hPQ ↦ hPQ.elim (h₁ hv) (h₂ hv)⟩),
      eq_false fun h ↦ p.serial.elim fun v hv ↦ h hv trivial⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨⟨Bool, .univ, true⟩, ⟨true, trivial⟩⟩)).2.1
    {true} {false}
  revert this
  simp only [SetRel.core, Set.mem_ofPred_eq, Set.inf_eq_inter, sup_Prop_eq, eq_iff_iff]
  decide

/-! ### Non-triviality

Each downward entailing licenser has an operator that is not upward entailing, so it is not
downward entailing by being constant. -/

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

theorem not_isStrawsonUE_withoutClause : ¬ withoutClause.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Unit, Set.univ⟩, fun h ↦
    (h (bot_le (a := ⊤)) (Set.mem_sdiff_of_mem (Set.mem_univ ()) (Set.notMem_empty ()))).2 trivial⟩

theorem not_isStrawsonUE_beforeClause : ¬ beforeClause.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨ℕ, {NonemptyInterval.pure 0}⟩, fun h ↦
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

theorem not_isStrawsonUE_onlyFocus : ¬ onlyFocus.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Bool, Unit, true⟩, not_isStrawsonUE_only⟩

theorem not_isStrawsonUE_adversative : ¬ adversative.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Fin 3, fun _ ↦ {0}, fun _ ↦ .univ, fun _ ↦ {(· = 1)}⟩,
    Desire.BestWorlds.not_isStrawsonUE_regret⟩

theorem not_isStrawsonUE_superlative : ¬ superlative.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Bool, Unit, ℕ, fun _ ↦ 0, true⟩, Degree.not_isStrawsonUE_superlative⟩

theorem not_isStrawsonUE_conditionalAntecedent : ¬ conditionalAntecedent.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨Unit, Bool, fun _ ↦ .univ, {true}⟩,
    Conditional.not_isStrawsonUE_horizonCounterfactual⟩

theorem not_isStrawsonUE_sinceTemporal : ¬ sinceTemporal.licenser.IsStrawsonUE :=
  not_forall.2 ⟨⟨ℤ, (· - 5)⟩, not_isStrawsonUE_since⟩

/-! ### Scalar licensers

*Few* and *at most n* exhaustified against their stronger scale-mates assert *some*, so they are
not downward entailing ([gajewski-2011]'s (45), (48)). -/

theorem not_holds_exhaustified_few : ¬ few.licenser.exhaustified.Holds .anti := fun h ↦ by
  have hA : ¬ Det.few (Set.univ : Set (Fin 3)) ≤ Det.no Set.univ := fun hle ↦
    absurd (hle {0} (by decide)) (by decide)
  have hanti : Antitone (Det.exhaustified Det.few {Det.no} (Set.univ : Set (Fin 3))) :=
    Signature.holdsFor_anti_iff.mp (h ⟨⟨Fin 3, Set.univ⟩⟩)
  refine Det.not_exhaustified_of_not_le (Set.mem_singleton _) (fun _ _ hx ↦ hx) hA
    (hanti (a := ∅) (b := {0}) (Set.empty_subset _) (Det.exhaustified_iff.2 ⟨by decide, ?_⟩))
  rintro _ rfl hno
  exact absurd hno (by decide)

theorem not_holds_exhaustified_atMost : ¬ atMost.licenser.exhaustified.Holds .anti := fun h ↦ by
  have hA : ¬ Det.atMost 1 (Set.univ : Set Bool) ≤ Det.atMost 0 Set.univ := fun hle ↦
    absurd (hle {true} (by decide)) (by decide)
  have hanti : Antitone (Det.exhaustified (Det.atMost 1) {Det.atMost 0} (Set.univ : Set Bool)) :=
    Signature.holdsFor_anti_iff.mp (h ⟨⟨⟨Bool, Set.univ⟩⟩, 1⟩)
  refine Det.not_exhaustified_of_not_le (Set.mem_singleton _)
    (show Det.atMost 0 (Set.univ : Set Bool) ∅ by decide) hA
    (hanti (a := ∅) (b := {true}) (Set.empty_subset _) (Det.exhaustified_iff.2 ⟨by decide, ?_⟩))
  rintro _ rfl hle
  exact absurd hle (by decide)

/-! ### Strawson licensers -/

theorem isStrawsonDE_onlyFocus : onlyFocus.licenser.IsStrawsonDE := fun p ↦ isStrawsonDE_only p.x

theorem not_holds_onlyFocus : ¬ onlyFocus.licenser.Holds .anti := fun h ↦
  not_antitone_posSupport_only (Signature.holdsFor_anti_iff.mp (h ⟨Bool, Unit, true⟩))

theorem isStrawsonDE_adversative : adversative.licenser.IsStrawsonDE := fun p ↦
  Desire.BestWorlds.isStrawsonDE_regret p.dox p.base p.g

theorem not_holds_adversative : ¬ adversative.licenser.Holds .anti := fun h ↦
  Desire.BestWorlds.not_antitone_posSupport_regret (Signature.holdsFor_anti_iff.mp
    (h ⟨Bool, fun _ ↦ {true}, fun _ ↦ .univ, fun _ ↦ {(· = false)}⟩))

theorem isStrawsonDE_superlative : superlative.licenser.IsStrawsonDE := fun p ↦
  Degree.isStrawsonDE_superlative p.μ p.x

theorem not_holds_superlative : ¬ superlative.licenser.Holds .anti := fun h ↦
  Degree.not_antitone_posSupport_superlative (Signature.holdsFor_anti_iff.mp
    (h ⟨Unit, Unit, ℕ, fun _ ↦ 0, ()⟩))

theorem isStrawsonDE_conditionalAntecedent : conditionalAntecedent.licenser.IsStrawsonDE :=
  fun p ↦ Conditional.isStrawsonDE_horizonCounterfactual p.horizon p.q

theorem not_holds_conditionalAntecedent : ¬ conditionalAntecedent.licenser.Holds .anti := fun h ↦
  Conditional.not_antitone_posSupport_horizonCounterfactual (Signature.holdsFor_anti_iff.mp
    (h ⟨Unit, Unit, fun _ ↦ .univ, .univ⟩))

theorem isStrawsonDE_sinceTemporal : sinceTemporal.licenser.IsStrawsonDE := fun p ↦
  isStrawsonDE_since p.ago

theorem not_holds_sinceTemporal : ¬ sinceTemporal.licenser.Holds .anti := fun h ↦
  not_antitone_posSupport_since (Signature.holdsFor_anti_iff.mp (h ⟨ℤ, (· - 5)⟩))

/-! ### Modal licensers and questions -/

/-- Over three worlds, the first accessing the other two, each the one world where one of two
individuals is a witness. -/
private def branching : SetRel (Fin 3) (Fin 3) := {p | p.1 = 0 ∧ p.2 ≠ 0}

private def witnessAt (d : Fin 2) : Set (Fin 3) := {d.succ}

theorem licensesFreeChoice_necessityFamily : (Licenser.modal necessityFamily).LicensesFreeChoice :=
  ⟨⟨Fin 3, branching⟩, Fin 2, witnessAt, .univ, by decide, 0,
    Exhaustification.mem_oMinus_of_forall_ne
      (fun v hv ↦ by
        obtain ⟨d, rfl⟩ := Fin.exists_succ_eq.2 hv.2
        exact Set.mem_iUnion₂.2 ⟨d, Finset.mem_univ _, rfl⟩)
      fun S _ hne ⟨d, hd⟩ h ↦ by
        have hd' : (d + 1) ∉ S := fun h' ↦ hne (Finset.eq_univ_iff_forall.2 fun x ↦ by
          fin_cases d <;> fin_cases x <;> simp_all)
        have := @h (d + 1).succ ⟨rfl, Fin.succ_ne_zero (d + 1)⟩
        obtain ⟨e, he, hev⟩ := Set.mem_iUnion₂.1 this
        exact hd' ((Fin.succ_injective _ (Set.mem_singleton_iff.1 hev)).symm ▸ he)⟩

theorem licensesFreeChoice_modalPossibility : modalPossibility.licenser.LicensesFreeChoice :=
  ⟨⟨Fin 3, branching⟩, Fin 2, witnessAt, .univ, by decide, 0, by
    show 0 ∈ Exhaustification.oMinus
      (fun S ↦ branching.preimage (⋃ d ∈ S, witnessAt d)) .univ
    rw [Exhaustification.oMinus_preimage_biUnion witnessAt branching Finset.univ_nonempty]
    exact Set.mem_iInter₂.2 fun d _ ↦ ⟨d.succ, rfl, rfl, d.succ_ne_zero⟩⟩

end LicensingContext

end PolarityItem
