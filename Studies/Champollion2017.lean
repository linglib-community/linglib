module

public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Events.Basic
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Fragments.English.Verbs.Inventory
public import Studies.Krifka1998

/-!
# Champollion 2017: distributivity as a bridge between aspect and measurement

Champollion's *Parts of a Whole* unifies predicative distributivity, atelicity and
pseudopartitive measurement under one property, stratified reference: a predicate applies to an
event that divides exhaustively into parts the predicate also applies to, along some dimension.
The dimension varies, thematic roles for distributivity, run time for the *for*-adverbial and a
measure for the pseudopartitive, while the property is defined once. Lexical cumulativity, which
the book assumes throughout, entails Krifka's cumulativity, and atelicity along the run time is
a Schwarzschild cover into parts with properly smaller run times. Against Krifka's subregion
account of *for*-adverbials, the book's back-and-forth scenario has stratified reference and
violates the subregion presupposition. The per-verb distributivity facts are meaning postulates,
stated over the Fragment verbs' denotations.

## Main definitions

* `StratifiedReference`: an event divides into parts the predicate applies to, whose images along
  a dimension stand in a granularity relation to the event's.
* `DistributiveReference`: stratified reference along a thematic role with atomic granularity.
* `SubintervalReference`: stratified reference along the run time with proper subintervals.
* `MeasurementReference`: stratified reference along a measure with smaller values.
* `Verb.StratifiesOver`: a verb's denotation has distributive reference along a role.
* `LexicallyCumulative`: a predicate is a fixed point of algebraic closure.
* `ChampollionPostulates`: the per-verb distributivity postulates.

## Main results

* `lexicallyCumulative_imp_cum`: lexical cumulativity entails Krifka's `CUM`.
* `subintervalReference_iff_cover`: atelicity is a finite cover into proper-subinterval parts.
* `stratifiedReference_of_divisiveness`: on a temporally separable event, Krifka's divisiveness
  clause gives stratified reference along the run time.
* `pushCarts_stratified`: the back-and-forth event of Figure 6.2 has stratified reference.
* `pushCarts_not_subregion`: that event fails the subregion presupposition.

## Implementation notes

* Vendler classes are not among the book's primitives; its atelicity diagnostic is the
  subinterval-reference test.
* The granularity is a binary relation between the image of a part and the image of the whole,
  where the book has a unary predicate built from the whole, so that the three specializations
  are instances of one definition.
* Stratified reference along the runtime neither entails nor follows from Krifka's `CUM`: the
  book takes every verb to be cumulative, telic ones included, and a predicate of events of
  bounded length has stratified reference over dense time without being closed under sums.
* The runtime dimension of chapter 6 is any monotone map into a part order of times, so the
  stratified reference in play is the generic `StratifiedReference τ (· < ·)` rather than the
  interval-runtime `SubintervalReference`; runtimes of back-and-forth events are discontinuous
  (the chapter's footnote on the scenario), and the finite model takes them to be sets of
  instants.
* The presupposition (28) is stated as the chapter states it, with the universal clause over the
  temporal parts of the event; the reflexive case is the predicate at the event itself.

## References

* [champollion-2017]
-/

@[expose] public section

namespace Champollion2017

open Event (τ)

open _root_.Mereology Aspect

/-! ### Stratified reference ([champollion-2017] eq. 16/17) -/

/-- `StratifiedReference d γ P x` holds when `x` is a sum of `P`-parts whose images under the
dimension `d` stand in the granularity relation `γ` to the image of `x`, the stratified reference
of [champollion-2017] eq. (16) with the granularity of eq. (17) made binary. -/
def StratifiedReference {α β : Type*} [SemilatticeSup α]
    (d : α → β) (γ : β → β → Prop) (P : α → Prop) (x : α) : Prop :=
  AlgClosure (fun y ↦ P y ∧ γ (d y) (d x)) x

/-! ### Universal stratified reference -/

/-- `P` has universal stratified reference along `d` at granularity `γ` when every `P`-entity
    has stratified reference. -/
def StratifiedReferenceUniv {α β : Type*} [SemilatticeSup α]
    (d : α → β) (γ : β → β → Prop) (P : α → Prop) : Prop :=
  ∀ x, P x → StratifiedReference d γ P x

/-! ### Atomic granularity (shared γ) -/

/-- Atomic granularity holds when the inner image is an atom of the dimension, the granularity of
distributive reference along a thematic role. -/
def AtomicGranularity {β : Type*} [PartialOrder β] : β → β → Prop :=
  fun inner _outer ↦ Atom inner

/-! ### Stratified Distributive StratifiedReference ([champollion-2017] eq. 24) -/

/-- Stratified distributive reference is stratified reference whose dimension is a thematic
    role θ and whose granularity is `Atom` on the inner image, the outer being unused since
    atomicity is an absolute property ([champollion-2017] eq. (24)). It captures
    distributivity, as "The boys each saw a movie" distributes over atomic agents. -/
def DistributiveReference {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) (x : α) : Prop :=
  StratifiedReference θ AtomicGranularity P x

/-- `P` has universal distributive reference when every `P`-entity distributes along θ. -/
def DistributiveReferenceUniv {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (P : α → Prop) : Prop :=
  ∀ x, P x → DistributiveReference θ P x

/-! ### Relational distributive reference (neo-Davidsonian roles)

Champollion's `DistributiveReference` takes a *functional* thematic role
`θ : α → Entity` (the unique role-filler). linglib's neo-Davidsonian roles
are *relational*, `Entity → Event → Prop`,
`Agent(a, e)` — with thematic uniqueness available as
`Mereology.UP`. `RelationalDistributiveReference` is the relational
form, so the distributivity property composes directly with a
`ThematicFrame` / `Verb.denote` without picking a role function. It
coincides with the functional form on a role's graph
(`relationalDistributiveReference_graph`). -/

/-- Relational distributive reference takes the role to be a neo-Davidsonian relation `R` and
counts a part when it has an atomic `R`-filler. -/
def RelationalDistributiveReference {Entity α : Type*} [PartialOrder Entity]
    [SemilatticeSup α] (R : Entity → α → Prop) (P : α → Prop) (x : α) : Prop :=
  AlgClosure (fun y ↦ P y ∧ ∃ a, R a y ∧ Atom a) x

/-- `P` has universal relational distributive reference when every `P`-element distributes
    along `R`. -/
def RelationalDistributiveReferenceUniv {Entity α : Type*} [PartialOrder Entity]
    [SemilatticeSup α] (R : Entity → α → Prop) (P : α → Prop) : Prop :=
  ∀ x, P x → RelationalDistributiveReference R P x

theorem relationalDistributiveReference_mono {Entity α : Type*}
    [PartialOrder Entity] [SemilatticeSup α]
    {R : Entity → α → Prop} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, RelationalDistributiveReference R P x →
      RelationalDistributiveReference R Q x := by
  intro x hx
  exact algClosure_mono (fun y ⟨hp, ha⟩ ↦ ⟨h y hp, ha⟩) x hx

theorem relationalDistributiveReference_graph {Entity α : Type*}
    [PartialOrder Entity] [SemilatticeSup α]
    {θ : α → Entity} {P : α → Prop} {x : α} :
    RelationalDistributiveReference (fun a y ↦ θ y = a) P x ↔
      DistributiveReference θ P x := by
  unfold RelationalDistributiveReference DistributiveReference StratifiedReference
    AtomicGranularity
  simp only [exists_eq_left']

/-! ### Stratified Subinterval StratifiedReference ([champollion-2017] eq. 38) -/

/-- Proper-subinterval granularity holds when the inner run time is a proper subinterval of the
outer one. -/
def SubintervalGranularity {T : Type*} [LinearOrder T]
    (inner outer : NonemptyInterval T) : Prop :=
  inner < outer

/-- Stratified subinterval reference is stratified reference whose dimension is the runtime τ
    and whose granularity is proper subinterval, so `SubintervalReference P e` holds iff `e` can
    be built from `P`-parts with runtimes properly included in `τ e` ([champollion-2017]
    eq. (38)). It captures atelicity, the predicates compatible with *for*-adverbials having
    subinterval reference. -/
def SubintervalReference {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
    [SemilatticeSup E]
    (P : E → Prop) (e : E) : Prop :=
  StratifiedReference τ SubintervalGranularity P e

/-- `P` has universal subinterval reference when every `P`-event has subinterval reference. -/
def SubintervalReferenceUniv {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
    [SemilatticeSup E]
    (P : E → Prop) : Prop :=
  ∀ e, P e → SubintervalReference P e

/-! ### Stratified Measurement StratifiedReference -/

/-! **`MeasurementReference`** is [champollion-2017]'s *stratified
    measurement reference* (his named property and abbreviation): Def 61
    in the Ch 4 §4.6 unification, with final universal/restricted forms
    Defs 52–53 in Ch 7 §7.4, written as `SR_{μ, λd.d < μ(x)}` (*thirty
    liters of water*, *five feet of snow*, *two degrees Celsius of global
    warming*).

    The strict-less-than granularity is Champollion's faithful translation
    of [schwarzschild-2006]'s monotonic measure-function predicate
    (Ch 7 eq. 8: `μ` is monotonic iff `a < b → μ(a) < μ(b)`), with the
    extensive/intensive measure-function distinction ([krifka-1998])
    reduced to whether the resulting measurement-reference presupposition
    is satisfiable on the given substance noun.
-/

/-- Stratified measurement reference is stratified reference whose dimension is a measure
    function μ and whose granularity is strict less-than on the scale, so
    `MeasurementReference μ P x` holds iff `x` can be decomposed into `P`-parts with strictly
    smaller μ-values. -/
def MeasurementReference {α β : Type*} [SemilatticeSup α] [Preorder β]
    (μ : α → β) (P : α → Prop) (x : α) : Prop :=
  StratifiedReference μ (· < ·) P x

/-- `P` has universal measurement reference when every `P`-entity has measurement reference
    along μ. -/
def MeasurementReferenceUniv {α β : Type*} [SemilatticeSup α] [Preorder β]
    (μ : α → β) (P : α → Prop) : Prop :=
  ∀ x, P x → MeasurementReference μ P x

/-! ### Distributivity Constraint -/

/-- The Distributivity Constraint of [champollion-2017] accepts a distributive construction with
share `Share`, map `Map` and granularity `gran` describing `x` exactly when the share has
stratified reference along the map at that granularity. Adverbial *each*, *for*-adverbials and
pseudopartitives differ only in the three parameters. -/
abbrev DistributivityConstraint {α β : Type*} [SemilatticeSup α]
    (Map : α → β) (gran : β → β → Prop) (Share : α → Prop) (x : α) : Prop :=
  StratifiedReference Map gran Share x

/-! ### Construction Instances -/

/-- Adverbial *each* requires distributive reference along a thematic role. -/
abbrev eachConstr {α β : Type*} [SemilatticeSup α] [PartialOrder β]
    (θ : α → β) (Share : α → Prop) (x : α) : Prop :=
  DistributiveReference θ Share x

/-- A *for*-adverbial requires its predicate to have subinterval reference. -/
abbrev forConstr {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
    [SemilatticeSup E]
    (Share : E → Prop) (e : E) : Prop :=
  SubintervalReference Share e

/-! ### Key Theorems -/

theorem stratifiedReferenceUniv_entails_restricted {α β : Type*} [SemilatticeSup α]
    {d : α → β} {γ : β → β → Prop} {P : α → Prop}
    (h : StratifiedReferenceUniv d γ P) {x : α} (hx : P x) : StratifiedReference d γ P x :=
  h x hx

theorem stratifiedReference_trivial_granularity {α β : Type*} [SemilatticeSup α]
    {d : α → β} {P : α → Prop} :
    StratifiedReferenceUniv d (fun _ _ ↦ True) P := by
  intro x hx
  exact AlgClosure.base ⟨hx, trivial⟩

theorem distributiveReference_mono {α β : Type*} [SemilatticeSup α]
    [PartialOrder β]
    {θ : α → β} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, DistributiveReference θ P x → DistributiveReference θ Q x := by
  intro x hx
  exact algClosure_mono (fun y ⟨hp, hg⟩ ↦ ⟨h y hp, hg⟩) x hx

theorem stratifiedReference_mono {α β : Type*} [SemilatticeSup α]
    {d : α → β} {γ : β → β → Prop} {P Q : α → Prop} (h : ∀ x, P x → Q x) :
    ∀ x, StratifiedReference d γ P x → StratifiedReference d γ Q x := by
  intro x hx
  exact algClosure_mono (fun y ⟨hp, hg⟩ ↦ ⟨h y hp, hg⟩) x hx

theorem stratifiedReference_of_refl_granularity {α β : Type*} [SemilatticeSup α]
    {d : α → β} {γ : β → β → Prop} (hRefl : ∀ b, γ b b)
    {P : α → Prop} {x : α} (hx : P x) : StratifiedReference d γ P x :=
  AlgClosure.base ⟨hx, hRefl (d x)⟩

theorem stratifiedReference_join {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (d : SupHom α β)
    {γ : β → β → Prop}
    (hMono : ∀ a b₁ b₂, γ a b₁ → b₁ ≤ b₂ → γ a b₂)
    {P : α → Prop} {x y : α}
    (hx : StratifiedReference d γ P x) (hy : StratifiedReference d γ P y) :
    StratifiedReference d γ P (x ⊔ y) := by
  unfold StratifiedReference at hx hy ⊢
  -- The closure structure already gives closure under sum (algClosure_cum);
  -- we just weaken the granularity witness via monotonicity to compare
  -- against the joined outer dimension.
  have hxy : AlgClosure (fun z ↦ P z ∧ γ (d z) (d x ⊔ d y)) (x ⊔ y) := by
    have hx' : AlgClosure (fun z ↦ P z ∧ γ (d z) (d x ⊔ d y)) x := by
      exact algClosure_mono
        (fun z ⟨hp, hg⟩ ↦ ⟨hp, hMono _ _ _ hg le_sup_left⟩) x hx
    have hy' : AlgClosure (fun z ↦ P z ∧ γ (d z) (d x ⊔ d y)) y := by
      exact algClosure_mono
        (fun z ⟨hp, hg⟩ ↦ ⟨hp, hMono _ _ _ hg le_sup_right⟩) y hy
    exact AlgClosure.sum hx' hy'
  rw [map_sup]
  exact hxy

/-! ### Aspect Bridge (subinterval reference ↔ atelicity) -/

theorem forAdverbial_requires_subintervalReference
    {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
    [SemilatticeSup E]
    {P : E → Prop}
    (h_for_ok : SubintervalReferenceUniv P) :
    ∀ e, P e → SubintervalReference P e :=
  h_for_ok

theorem qua_incompatible_with_subintervalReference
    {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
    [SemilatticeSup E]
    {P : E → Prop}
    (hQua : QUA P)
    {e : E} (he : P e) (hSub : SubintervalReference P e) :
    False := by
  obtain ⟨a, ⟨hPa, hGran⟩, hle⟩ := algClosure_has_base hSub
  have hne : a ≠ e := by
    intro heq; rw [heq] at hGran
    exact lt_irrefl _ hGran
  exact hQua hPa he hne hle

/-! ### for-Adverbial Compatibility -/

/-- *V for δ* holds of an event of `V` whose run time is `δ` and at which `V` has subinterval
reference, [champollion-2017]'s entry for the *for*-adverbial, eq. (72). -/
def forAdverbialMeaning {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
    [SemilatticeSup E]
    (V : E → Prop) (duration : NonemptyInterval T) (e : E) : Prop :=
  V e ∧ τ e = duration ∧ SubintervalReference V e

theorem in_adverbial_incompatible_with_subintervalReference
    {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
    [SemilatticeSup E]
    {P : E → Prop}
    (hQua : QUA P)
    {e₁ e₂ : E} (he₁ : P e₁) (_he₂ : P e₂) (_hne : e₁ ≠ e₂) :
    ¬ SubintervalReferenceUniv P := by
  intro hSub
  exact qua_incompatible_with_subintervalReference hQua he₁ (hSub e₁ he₁)

end Champollion2017

namespace Verb

open _root_.Aspect Champollion2017

/-! ### Verb distributivity

Whether a verb distributes over the atomic fillers of a thematic role is a property of its event
denotation, not a feature it carries. -/

variable {Entity E : Type*} [PartialOrder Entity] [SemilatticeSup E]

/-- A verb stratifies over the atomic fillers of role `R` when the event predicate that the
interpretation `V` assigns it has relational stratified distributive reference along `R`. -/
def StratifiesOver (v : Verb) (V : Verb → E → Prop) (R : Entity → E → Prop) :
    Prop :=
  RelationalDistributiveReferenceUniv R (V v)

end Verb

namespace Champollion2017

open English
open English.Verbs hiding Verb
open _root_.Mereology
open Aspect

/-! ### §2.7.2 algebraic substrate -/

section ThematicRolesAndCumulativity

/-- A predicate is lexically cumulative when it is a fixed point of the algebraic closure
operator. -/
def LexicallyCumulative {α : Type*} [SemilatticeSup α] (P : α → Prop) : Prop :=
  ∀ x, AlgClosure P x ↔ P x

/-- Lexical cumulativity entails Krifka's `CUM` (closure under binary join). -/
theorem lexicallyCumulative_imp_cum {α : Type*} [SemilatticeSup α]
    {P : α → Prop} (h : LexicallyCumulative P) : CUM P := by
  intro x hPx y hPy
  exact (h _).mp (AlgClosure.sum (AlgClosure.base hPx) (AlgClosure.base hPy))

end ThematicRolesAndCumulativity

/-! ### Distributivity as meaning postulates

The book's per-verb distributivity facts are lexical meaning postulates in Hoeksema's sense, not
theorems; they are stated here over the Fragment verbs' denotations. -/

section Distributivity
variable {Entity E : Type*} [PartialOrder Entity] [SemilatticeSup E]

/-- `ChampollionPostulates` records the book's postulates on the distributivity of verbs, over an
interpretation `V` of the fragment's verbs as event predicates and the agent and theme roles. *See*
distributes on both roles and *kill* on its theme only, since a member of the posse need not have
killed anyone, and *meet* does not distribute on its agent. -/
structure ChampollionPostulates (V : Verb → E → Prop)
    (agentRole themeRole : Entity → E → Prop) : Prop where
  see_distributes_agent : see.toVerb.StratifiesOver V agentRole
  see_distributes_theme : see.toVerb.StratifiesOver V themeRole
  kill_distributes_theme : kill.toVerb.StratifiesOver V themeRole
  kill_not_distributes_agent : ¬ kill.toVerb.StratifiesOver V agentRole
  meet_not_distributes_agent : ¬ meet.toVerb.StratifiesOver V agentRole

end Distributivity

/-! ### Atelicity as a Schwarzschild cover (§5.4) -/

/-- A predicate `P` has stratified subinterval reference at `e` iff `e` is the sum of a finite
Schwarzschild cover into proper-subinterval `P`-parts, the book's theorem at the runtime
dimension. -/
theorem subintervalReference_iff_cover {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
    [SemilatticeSup E] {P : E → Prop} {e : E} :
    SubintervalReference P e ↔
      ∃ (parts : Finset E) (hne : parts.Nonempty),
        (∀ p ∈ parts, P p ∧ Event.τ p < Event.τ e) ∧ parts.sup' hne id = e := by
  unfold SubintervalReference StratifiedReference SubintervalGranularity
  exact algClosure_iff_exists_sup' _ _

/-! ### Aspect and space: the subregion and strata approaches (§6.3–6.4) -/

section Subregion

open Krifka1998

variable {α T : Type*} [SemilatticeSup α] [PartialOrder T] (τ : α → T) (P : α → Prop)

/-- The subregion presupposition (28), which the chapter attributes to [krifka-1998]'s
*for*-adverbial, holds when the event has a temporal part and every temporal part of it falls
under the predicate. -/
def SubregionPresup (e : α) : Prop :=
  (∃ e', IsTemporalPart τ e' e) ∧ ∀ e', IsTemporalPart τ e' e → P e'

variable {τ P}

/-- On an event that splits into two parts with non-overlapping, non-null runtimes, the
divisiveness clause of the subregion presupposition yields stratified reference along the
runtime: the two parts are each other's temporal siblings, so both fall under the predicate,
and each has a properly smaller runtime. -/
theorem stratifiedReference_of_divisiveness (hτ : Monotone τ) {a b : α}
    (hov : ¬ Overlap (τ a) (τ b)) (ha : ¬ IsBot (τ a)) (hb : ¬ IsBot (τ b))
    (hdiv : ∀ e', IsTemporalPart τ e' (a ⊔ b) → P e') :
    StratifiedReference τ (· < ·) P (a ⊔ b) :=
  .sum (.base ⟨hdiv a ⟨le_sup_left, b, le_sup_right, hov⟩, lt_of_le_of_ne (hτ le_sup_left)
      fun h ↦ hov ⟨τ b, hb, h ▸ hτ le_sup_right, le_rfl⟩⟩)
    (.base ⟨hdiv b ⟨le_sup_right, a, le_sup_left, fun o ↦ hov o.symm⟩,
      lt_of_le_of_ne (hτ le_sup_right) fun h ↦ hov ⟨τ a, ha, le_rfl, h ▸ hτ le_sup_left⟩⟩)

/-- The back-and-forth scenario has four trips of two legs each, a leg at each instant, the even
legs from the lot halfway to the store and the odd legs on to the store. An event is a set of
legs and its runtime the set of their instants. -/
abbrev Leg := Fin 8

/-- *push carts all the way to the store* holds of a nonempty event whose path reaches the
store, that is, one containing a leg on to the store. -/
def PushCartsToStore (e : Finset Leg) : Prop := e.Nonempty ∧ ∃ k ∈ e, k.val % 2 = 1

instance : DecidablePred PushCartsToStore := fun _ ↦ by unfold PushCartsToStore; infer_instance

/-- The cart-pushing event divides along time into four trips each reaching the store, so the
strata-based account admits the *for*-adverbial (Figure 6.2a). -/
theorem pushCarts_stratified :
    StratifiedReference id (· < ·) PushCartsToStore (Finset.univ : Finset Leg) :=
  (algClosure_iff_exists_sup' _ _).2
    ⟨{{0, 1}, {2, 3}, {4, 5}, {6, 7}}, by decide, by decide +kernel, by decide +kernel⟩

/-- The halfway legs of §6.4.1 do not reach the store, so the subregion presupposition fails (Figure
6.2b). -/
theorem pushCarts_not_subregion :
    ¬ SubregionPresup id PushCartsToStore (Finset.univ : Finset Leg) := fun ⟨_, hdiv⟩ ↦
  absurd (hdiv {0, 2, 4, 6} ⟨by decide, {1, 3, 5, 7}, by decide,
    fun h ↦ overlap_iff_not_disjoint.1 h (by decide)⟩) (by decide)

end Subregion

end Champollion2017
