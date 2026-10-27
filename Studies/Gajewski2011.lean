module

public import Linglib.Logic.Natural.Strawson
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Data.Examples.Gajewski2011

/-!
# Gajewski (2011): Licensing strong NPIs

Gajewski explains why weak negative polarity items (*any*, *ever*) and strong ones (*in weeks*,
*either*, *until*) part ways under *only*, conditional antecedents and *sorry*. These operators
are Strawson anti-additive, the Strawson form of the anti-additivity Zwarts held strong items to
need, yet they license only weak items. The two classes inspect different meanings: a weak item
needs the plain meaning Strawson downward entailing, while a strong item needs the meaning
enriched by Chierchia's exhaustivity operator, presuppositions included, downward entailing
outright. A determiner at the bottom of its Horn scale, *no*, is its own enriched meaning and
licenses both; one above the bottom exhaustifies to a meaning with an upward-entailing conjunct;
and a presupposition trigger's full meaning fails plain downward entailment.

## Main results

* `strawsonAA_not_sufficient`: *only*, *would* and *sorry* are Strawson anti-additive, yet their
  meanings are not downward entailing outright.
* `licensed_iff`: *no* is the only licenser of strong items and *some* the only non-licenser of
  weak ones, and `rows_predicted` checks this against the paper's judgments.
* `isIntolerant_of_isAntiAdditive`, `few_isIntolerant`, `atMostThree_not_isIntolerant`: Horn's
  Intolerance sits strictly between anti-additivity and downward entailment.

## Implementation notes

* Entailment between scale-mates holds the restrictor fixed and quantifies over scopes, so *no*
  entails *not every* whenever the restrictor is nonempty, which is what makes *no* the bottom
  of its scale; letting the restrictor vary would break the entailment at an empty restrictor.
  The scale is the pair of ends the paper's computation of exhaustified *not every* uses.
* The presupposition triggers have no scale-mates, so their enriched meaning is their full
  meaning, presupposition included, and the strong principle asks for its plain downward
  entailment. The operators are von Fintel's, with their owners, and their Strawson properties
  are in `Logic/Natural/Strawson.lean`.
* *At most five* against *at most four*, and the cardinal *fewer than four* of the
  scale-truncation discussion, are checked on a six-element domain.

## References

* [gajewski-2011]
* [von-fintel-1999]
* [zwarts-1998]
* [chierchia-2006]
* [horn-1989]
-/

@[expose] public section

namespace Gajewski2011

open NaturalLogic Presupposition Quantifier Quantifier.GQ Desire.BestWorlds

variable {α : Type*}

/-! ### Enriched meanings -/

theorem exhaustified_notEvery {A : α → Prop} {x y : α} (hx : A x) (hy : A y) (hxy : x ≠ y) :
    exhaustified (everyᶜ) {no} A = fun P ↦ GQ.some A P ∧ everyᶜ A P := by
  funext P
  refine propext (exhaustified_iff.trans
    ⟨fun ⟨hne, h⟩ ↦ ⟨?_, hne⟩, fun ⟨⟨z, hz, hPz⟩, hne⟩ ↦ ⟨hne, fun Q' hQ' hno ↦ ?_⟩⟩)
  · by_contra hsome
    exact h no (Set.mem_singleton _) (fun z hz hPz ↦ hsome ⟨z, hz, hPz⟩) (· = x)
      (fun hall ↦ hxy (hall y hy).symm) x hx rfl
  · exact ((Set.mem_singleton_iff.mp hQ' ▸ hno) z hz hPz).elim

theorem not_scopeAntitone_exhaustified {Q : GQ α} {C : Set (GQ α)} {A P : α → Prop}
    (hP : exhaustified Q C A P) (h : ¬ exhaustified Q C A (fun _ ↦ False)) :
    ¬ ScopeAntitone (exhaustified Q C) :=
  fun hde ↦ h (hde A (show ((fun _ : α ↦ False) : α → Prop) ≤ P from fun _ hf ↦ hf.elim) hP)

/-! ### The licensing principles -/

theorem no_strong : ScopeAntitone (exhaustified (no : GQ α) {everyᶜ}) := by
  rw [exhaustified_no]; exact scopeAntitone_no

/-- Exhaustified *not every* is not downward entailing, since at the empty scope the stronger
scale-mate *no* is true and excluded. -/
theorem notEvery_not_strong [Nontrivial α] :
    ¬ ScopeAntitone (exhaustified (everyᶜ : GQ α) {no}) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  refine not_scopeAntitone_exhaustified (A := fun _ ↦ True) (P := (· = x))
    (exhaustified_iff.2 ⟨fun h ↦ hxy (h y trivial).symm, fun Q' hQ' hno ↦
      ((Set.mem_singleton_iff.mp hQ' ▸ hno) x trivial rfl).elim⟩)
    (not_exhaustified_of_not_le (Set.mem_singleton _) (fun _ _ hf ↦ hf)
      fun hle ↦ hle (· = x) (fun h ↦ hxy (h y trivial).symm) x trivial rfl)

theorem some_not_strong [Nontrivial α] :
    ¬ ScopeAntitone (exhaustified (GQ.some : GQ α) {every}) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  exact not_scopeAntitone_exhaustified (A := fun _ ↦ True) (P := (· = x))
    (exhaustified_iff.2 ⟨⟨x, trivial, rfl⟩, fun Q' hQ' hev ↦
      (hxy ((Set.mem_singleton_iff.mp hQ' ▸ hev) y trivial).symm).elim⟩)
    fun h ↦ (exhaustified_iff.1 h).1.elim fun _ h ↦ h.2

theorem atMostFive_not_strong :
    ¬ ScopeAntitone (exhaustified (atMost 5 : GQ (Fin 6)) {atMost 4}) := by
  have h4 : ¬ atMost 4 (fun _ : Fin 6 ↦ True) (· ≠ 0) := by
    decide
  refine not_scopeAntitone_exhaustified (A := fun _ ↦ True) (P := (· ≠ 0))
    (exhaustified_iff.2 ⟨by decide,
      fun Q' hQ' h ↦ (h4 (Set.mem_singleton_iff.mp hQ' ▸ h)).elim⟩)
    (not_exhaustified_of_not_le (Set.mem_singleton _) (by decide)
      fun hle ↦ h4 (hle (· ≠ 0) (by decide)))

/-- The paper's licensers. -/
inductive Licenser
  | no | atMostFive | some | only | conditional | sorryThat
  deriving DecidableEq, Repr

/-- Weak items are *any* and *ever*, strong ones *in weeks*, *either* and *until*. -/
inductive Strength
  | weak | strong
  deriving DecidableEq, Repr

/-- The two licensing principles applied to a licenser's analysis, on which a weak item needs
the plain meaning Strawson downward entailing and a strong item needs the enriched meaning
downward entailing, which for a presupposition trigger without scale-mates is its full
meaning. -/
def Licensed : Licenser → Strength → Prop
  | .no, .weak => ∀ {α : Type}, ScopeAntitone (no : GQ α)
  | .no, .strong => ∀ {α : Type}, ScopeAntitone (exhaustified (no : GQ α) {everyᶜ})
  | .atMostFive, .weak => ∀ {α : Type} [Fintype α], ScopeAntitone (atMost (α := α) 5)
  | .atMostFive, .strong =>
      ∀ {α : Type} [Fintype α], ScopeAntitone (exhaustified (atMost (α := α) 5) {atMost 4})
  | .some, .weak => ∀ {α : Type}, ScopeAntitone (GQ.some : GQ α)
  | .some, .strong => ∀ {α : Type}, ScopeAntitone (exhaustified (GQ.some : GQ α) {every})
  | .only, .weak => ∀ {ι W : Type} (x : ι), IsStrawsonDE (only (W := W) x)
  | .only, .strong => ∀ {ι W : Type} (x : ι),
      Antitone fun P : ι → Set W ↦ posSupport (only x P)
  | .conditional, .weak => ∀ {W : Type} (horizon : W → Set W) (q : Set W),
      IsStrawsonDE (Conditional.horizonCounterfactual horizon · q)
  | .conditional, .strong => ∀ {W : Type} (horizon : W → Set W) (q : Set W),
      Antitone fun p ↦ posSupport (Conditional.horizonCounterfactual horizon p q)
  | .sorryThat, .weak => ∀ {W : Type} (dox base : W → Set W) (g : W → Set (W → Prop)),
      IsStrawsonDE (regret dox base g)
  | .sorryThat, .strong => ∀ {W : Type} (dox base : W → Set W) (g : W → Set (W → Prop)),
      Antitone fun p ↦ posSupport (regret dox base g p)

/-- The puzzle is that *only*, *would* and *sorry* are Strawson anti-additive, the Strawson form
of what strong items were held to need, yet none licenses them. -/
theorem strawsonAA_not_sufficient :
    (∀ {ι W : Type} (x : ι), IsStrawsonAntiAdditive (only (W := W) x)) ∧
      (∀ {W : Type} (horizon : W → Set W) (q : Set W),
        IsStrawsonAntiAdditive (Conditional.horizonCounterfactual horizon · q)) ∧
      (∀ {W : Type} (dox base : W → Set W) (g : W → Set (W → Prop)),
        IsStrawsonAntiAdditive (regret dox base g)) ∧
      ¬ Licensed .only .strong ∧ ¬ Licensed .conditional .strong ∧
        ¬ Licensed .sorryThat .strong :=
  ⟨isStrawsonAntiAdditive_only, Conditional.isStrawsonAntiAdditive_horizonCounterfactual,
    isStrawsonAntiAdditive_regret, fun h ↦ not_antitone_posSupport_only (h _),
    fun h ↦ Conditional.not_antitone_posSupport_horizonCounterfactual (h _ _),
    fun h ↦ not_antitone_posSupport_regret (h _ _ _)⟩

/-- *No* is the only one of the paper's licensers whose enriched meaning is downward
entailing. -/
theorem licensed_strong_iff (L : Licenser) : Licensed L .strong ↔ L = .no := by
  cases L with
  | no => exact iff_of_true (fun {_} ↦ no_strong) rfl
  | atMostFive => exact iff_of_false (fun h ↦ atMostFive_not_strong h) nofun
  | some => exact iff_of_false (fun h ↦ some_not_strong (α := Bool) h) nofun
  | only => exact iff_of_false strawsonAA_not_sufficient.2.2.2.1 nofun
  | conditional => exact iff_of_false strawsonAA_not_sufficient.2.2.2.2.1 nofun
  | sorryThat => exact iff_of_false strawsonAA_not_sufficient.2.2.2.2.2 nofun

/-- *Some* is the only one of the paper's licensers whose plain meaning is not Strawson
downward entailing. -/
theorem licensed_weak_iff (L : Licenser) : Licensed L .weak ↔ L ≠ .some := by
  cases L with
  | no => exact iff_of_true (fun {_} ↦ scopeAntitone_no) nofun
  | atMostFive => exact iff_of_true (fun {_} ↦ scopeAntitone_atMost 5) nofun
  | some =>
    refine iff_of_false (fun h ↦ ?_) (· rfl)
    exact (h (α := Bool) (fun _ ↦ True)
      (show ((fun _ : Bool ↦ False) : Bool → Prop) ≤ fun _ ↦ True from fun _ hf ↦ hf.elim)
      ⟨true, trivial, trivial⟩).elim fun _ h ↦ h.2
  | only => exact iff_of_true isStrawsonDE_only nofun
  | conditional => exact iff_of_true Conditional.isStrawsonDE_horizonCounterfactual nofun
  | sorryThat => exact iff_of_true isStrawsonDE_regret nofun

theorem licensed_iff (L : Licenser) (s : Strength) :
    Licensed L s ↔ (s = .weak ∧ L ≠ .some) ∨ (s = .strong ∧ L = .no) := by
  cases s <;> simp [licensed_weak_iff, licensed_strong_iff]

/-! ### The library's licensing

The library keeps Zwarts's strengths and asks for them of the meaning with the licenser's direct
implicature factored in, where the principles ask only for downward entailment of that meaning; on
the paper's licensers the two agree, as the paper's conjecture (48) has it for scale endpoints. -/

/-- The library's context for each licenser that has one. *Some* NP licenses nothing and has
none. -/
def Licenser.context : Licenser → Option PolarityItem.LicensingContext
  | .no => Option.some .nobody
  | .atMostFive => Option.some .atMost
  | .some => Option.none
  | .only => Option.some .onlyFocus
  | .conditional => Option.some .conditionalAntecedent
  | .sorryThat => Option.some .adversative

/-- An English item of each strength, *ever* and *in years*. -/
def Strength.item : Strength → PolarityItem
  | .weak => English.PolarityItems.ever
  | .strong => English.PolarityItems.inYears

theorem licensed_iff_licenses (L : Licenser) (s : Strength) {c : PolarityItem.LicensingContext}
    (hc : L.context = some c) : Licensed L s ↔ c.licenser.Licenses s.item := by
  rw [licensed_iff]
  cases L <;> cases s <;> simp only [Licenser.context, Option.some.injEq, reduceCtorEq] at hc <;>
    subst hc <;> simp [Strength.item, English.PolarityItems.ever, English.PolarityItems.inYears] <;>
    decide

/-! ### Intolerance -/

/-- A function of properties is trivial when it is constantly true or constantly false. -/
def IsTrivial (f : Set α → Prop) : Prop := (∀ x, f x) ∨ ∀ x, ¬ f x

/-- A nontrivial function of properties is Intolerant when it never accepts both a property and
its complement, as the items above the midpoint of their scale do ([horn-1989]). -/
def IsIntolerant (f : Set α → Prop) : Prop := ¬ IsTrivial f → ∀ x, ¬ f x ∨ ¬ f xᶜ

/-- Anti-additivity implies Intolerance, since accepting `x` and `xᶜ` means accepting everything. -/
theorem isIntolerant_of_isAntiAdditive {f : Set α → Prop} (h : IsAntiAdditive f) :
    IsIntolerant f := fun hnt x ↦ by
  by_contra hx
  rw [not_or, not_not, not_not] at hx
  have huniv := (isAntiAdditive_iff_gq.1 h x xᶜ).2 hx
  rw [Set.union_compl_self] at huniv
  exact hnt (Or.inl fun y ↦ h.antitone (Set.subset_univ y) huniv)

/-- Proportional *few* is Intolerant, since fewer than half in and fewer than half out is
impossible. -/
theorem few_isIntolerant (A : α → Prop) : IsIntolerant (few A) := fun _ x ↦ by
  by_contra hx
  rw [not_or, not_not, not_not, few_apply, few_apply] at hx
  obtain ⟨h₁, h₂⟩ := hx
  have e : {z | A z ∧ ¬ xᶜ z} = {z | A z ∧ x z} := Set.ext fun _ ↦ and_congr_right' not_not
  rw [e] at h₂
  exact absurd (h₁.trans h₂) (lt_irrefl _)

/-- Cardinal *fewer than four* is not Intolerant, since with six elements three are in and three
out. -/
theorem atMostThree_not_isIntolerant :
    ¬ IsIntolerant (atMost 3 (fun _ : Fin 6 ↦ True)) := fun h ↦ by
  let _ : DecidablePred (fun x : Fin 6 ↦ x < 3)ᶜ := fun z ↦ inferInstanceAs (Decidable (¬ z < 3))
  exact (h (fun ht ↦ ht.elim
      (fun h ↦ absurd (h (fun _ ↦ True)) (by decide))
      fun h ↦ h (fun _ ↦ False) (by decide)) (· < 3)).elim
    (· (by decide)) (· (by decide))

theorem few_not_rightAntiAdditive : ¬ RightAntiAdditive (few : GQ (Fin 4)) := fun h ↦
  absurd ((h (fun _ ↦ True) (· = 0) (· = 1)).mpr
      ⟨by decide, by decide⟩)
    (by decide)

/-! ### The paper's sentences -/

/-- A sentence of the paper records its licenser, the strength of its polarity item, and the
judgment. -/
structure Row where
  licenser : Licenser
  strength : Strength
  judgment : Judgment
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let licenser ← ex.parse? "licenser" [("no", Licenser.no), ("atMostFive", .atMostFive),
    ("some", .some), ("only", .only), ("conditional", .conditional), ("sorry", .sorryThat)]
  let strength ← ex.parse? "strength" [("weak", Strength.weak), ("strong", .strong)]
  pure ⟨licenser, strength, ex.judgment⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- Every judgment in the paper follows from the two licensing principles. -/
theorem rows_predicted :
    ∀ r ∈ rows, (r.judgment = .acceptable ↔ Licensed r.licenser r.strength) := by
  simp only [licensed_iff]
  decide

end Gajewski2011
