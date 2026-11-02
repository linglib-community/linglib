module

public import Linglib.Logic.Natural.Basic
public import Linglib.Semantics.PolarityItem.Licensing
public import Linglib.Semantics.PolarityItem.Basic
public import Linglib.Logic.Trivalent.Basic
public import Linglib.Semantics.Genericity.Normality
public import Studies.Ladusaw1979
public import Linglib.Data.Examples.KadmonLandman1993
public import Linglib.Fragments.English.PolarityItems
public import Mathlib.Data.Set.Basic
public import Linglib.Data.Examples.Readers

/-!
# Kadmon and Landman (1993): Any

Kadmon and Landman analyze *any CN* as the indefinite *a CN* with its domain widened along a
contextual dimension, licensed only when the widening makes the statement stronger, a condition
checked at the narrowest operator over the indefinite; free-choice *any* is the same item under a
generic interpretation. Widening weakens an existential, so strengthening holds
[exactly under an antitone context](##forall_strengthening_iff_antitone), which is why Ladusaw's
downward-entailing contexts license. Adversatives are
downward entailing on a constant perspective, a negated *because*-clause licenses only by
metalinguistic denial, and conditional antecedents strengthen once the implicit restriction is
fixed. The generic restriction is a vague property set whose precisifications give the normality
of GEN.

## Implementation notes

* The rows record, at the narrowest operator over *any*, a substrate `LicensingContext` where
  one exists and otherwise the local entailment signature; the settle-for-less and metalinguistic
  readings are the paper's own annotations, so `rows_agree` checks the paper's classification
  against its judgments rather than deriving those two readings.
* The vague-restriction apparatus is `Set`-based; on a finite enumeration of the
  precisifications, supervaluation is `SignType.supervaluation` over it.

## References

* [kadmon-landman-1993]
* [ladusaw-1979]
* [linebarger-1987]
* [fine-1975]
-/

@[expose] public section

namespace KadmonLandman1993

open NaturalLogic PolarityItem Ladusaw1979

/-! ### The strengthening condition

K&L's component (C): *any* is licensed only if widening creates a stronger
statement. For a context `C` and domains `D ⊆ D'`, the wide interpretation
must entail the narrow: `C (∃x∈D', Px) ⊆ C (∃x∈D, Px)`. This holds exactly
when `C` is antitone, which is why DE contexts license — and why widening in
UE contexts, where it weakens, leaves *any* unlicensed. -/

/-- K&L's strengthening condition holds when widening the domain `D` to `D'` in context `C`
creates a stronger statement, the wide interpretation entailing the narrow one. -/
def Strengthening {World Entity : Type*} (C : Set World → Set World) (D D' : Set Entity)
    (P : Entity → Set World) : Prop :=
  C (⋃ x ∈ D', P x) ⊆ C (⋃ x ∈ D, P x)

/-- In a DE (antitone) context, strengthening is automatic. K&L note that for many examples this
makes the same predictions as [ladusaw-1979], while explaining *why* DE contexts license, since
widening must strengthen and DE reverses entailment. -/
theorem de_satisfies_strengthening {World Entity : Type*} {C : Set World → Set World}
    (hDE : Antitone C) (D D' : Set Entity) (P : Entity → Set World)
    (hD : D ⊆ D') : Strengthening C D D' P :=
  hDE (Set.biUnion_subset_biUnion_left hD)

theorem forall_strengthening_iff_antitone {World : Type*} {C : Set World → Set World} :
    (∀ D D' : Set (Set World), D ⊆ D' → Strengthening C D D' id) ↔ Antitone C := by
  refine ⟨fun h a b hab ↦ ?_, fun hC D D' hD ↦ de_satisfies_strengthening hC D D' id hD⟩
  simpa [Strengthening, Set.union_eq_left.2 hab] using h {a} {b, a} (Set.subset_insert b {a})

/-- In a UE (monotone) context, widening *weakens* — the opposite of
strengthening. This is K&L's explanation for why *any* is out in plain
positive contexts. -/
theorem ue_widening_weakens {World Entity : Type*} {C : Set World → Set World}
    (hUE : Monotone C) (D D' : Set Entity) (P : Entity → Set World)
    (hD : D ⊆ D') : C (⋃ x ∈ D, P x) ⊆ C (⋃ x ∈ D', P x) :=
  hUE (Set.biUnion_subset_biUnion_left hD)

/-! ### Compatibility with Ladusaw 1979

Each context's licensing mechanism is read off its licenser (`PolarityItem.Licenser.mechanism`),
so this file's classification cannot drift from the semantics. K&L's classification refines
[ladusaw-1979]'s: every Ladusaw-DE context is a strengthening context, but K&L additionally
explain adversative predicates (DE on a constant perspective) and conditionals with implicit
restrictions. -/

/-- Ladusaw-DE contexts are K&L strengthening contexts; Ladusaw describes *where* NPIs occur, and
K&L explain *why*. -/
theorem ladusaw_de_is_kl_strengthening (L : PolarityItem.Licenser)
    (hDE : IsDownwardEntailing L) : L.LicensesByStrengthening :=
  Licenser.licensesByStrengthening_iff.2 (Licenser.isStrawsonDE_of_holds_anti hDE)

/-! ### Adversative predicates: *sorry* vs *glad*

K&L §3.3 reduce the adversatives to *want* on a constant perspective: being sorry that `A` is
wanting `A` false, and being glad that `A` is wanting `A`. Wanting a set empty entails wanting each
of its subsets empty, so *sorry* satisfies the strengthening condition; wanting a set inhabited does
not entail wanting each subset inhabited, so *glad* does not. -/

section Adversatives

variable {World : Type*} (best : World → Set World)

/-- On a perspective whose best worlds at `w` are `best w`, one wants `A` at `w` when those best
worlds are `A`-worlds. Being glad that `A` is wanting `A`. -/
def wants (A : Set World) : Set World := {w | best w ⊆ A}

/-- Being sorry that `A` is wanting `A` false on the same perspective. -/
def sorryThat (A : Set World) : Set World := wants best Aᶜ

/-- *Sorry* satisfies the strengthening condition, so it licenses *any*. -/
theorem strengthening_sorryThat {Entity : Type*} {D D' : Set Entity} (P : Entity → Set World)
    (hD : D ⊆ D') : Strengthening (sorryThat best) D D' P :=
  de_satisfies_strengthening (fun _ _ h _ hw ↦ hw.trans (Set.compl_subset_compl.2 h)) D D' P hD

end Adversatives

/-- *Glad* fails the strengthening condition, so it does not license *any*. The best world bought
the `false` car, so one is glad that some car was bought but not that the `true` car was. -/
theorem not_strengthening_wants :
    ¬ Strengthening (wants fun _ : Bool ↦ {false}) {true} .univ fun x ↦ {x} := by
  intro h
  have := h (a := true) (fun w _ ↦ Set.mem_biUnion (Set.mem_univ w) rfl) rfl
  simp at this

/-! ### Conditional antecedents

K&L §3.5 treat conditionals and adversatives as one pattern — DE with a
parameter held constant (the implicit restriction, resp. the perspective);
in mathlib terms, `Antitone (f param)` for fixed `param`. Under the
restrictor analysis of conditionals (cf. [kratzer-1986]), the antecedent of
conditional necessity is classically DE once the modal base is fixed, so
widening the antecedent domain strengthens the conditional. -/

-- (143)
theorem conditional_satisfies_strengthening {W : Type*}
    (domain : W → Set W) (β : Set W) :
    Antitone (Conditional.strictImp domain · β) :=
  fun _ _ h ↦ Conditional.strictImp_anti_left h

/-- A conditional with an implicit restriction (K&L's (147)) is true when every relevant case
satisfying the restriction and the antecedent satisfies the consequent. -/
def conditionalWithRestriction {Case : Type*}
    (restriction antecedent consequent : Case → Prop) : Prop :=
  ∀ c, restriction c → antecedent c → consequent c

/-- Widening always satisfies strengthening in conditional antecedents, though (140) does not entail
(141) (K&L §3.5.3). -/
theorem widening_satisfies_conditional_strengthening {Case : Type*}
    {R_narrow R_wide A_narrow A_wide consequent : Case → Prop}
    (hRestrWeaker : ∀ c, R_narrow c → R_wide c)
    (hAntWeaker : ∀ c, A_narrow c → A_wide c)
    (hWide : conditionalWithRestriction R_wide A_wide consequent) :
    conditionalWithRestriction R_narrow A_narrow consequent :=
  fun c hR hA ↦ hWide c (hRestrWeaker c hR) (hAntWeaker c hA)

/-! ### Negated because-clauses: metalinguistic licensing

K&L §3.4, contra [linebarger-1987]: `not because [S_]` is not DE (*because
[S_]* is not UE, so negating it yields no DE context), while `not because of
[NP_]` is DE and licenses *any* freely — (122)/(123) need no negative
implication. In `because [S_]`, *any* is licensed only metalinguistically:
the negation denies *because*'s factive presupposition, and *any* strengthens
that denial. Merely implying the denial is not enough — the rhetorical
conditional (132) can imply it but lacks the metalinguistic denial, and *any*
is out. This is the paper's only genuinely non-DE licensing mechanism. -/

/-! ### FC *any* as generic indefinite

K&L's component (FC): PS *any* is a regular indefinite, FC *any* a generic
indefinite; the apparent universal force of FC *any* emerges from genericity
plus widening (§4.3). The episodic/generic split below is projected from the
substrate's mechanism classification. K&L themselves analyze only plain
generics like (10) and tentatively extend to modals; routing
imperatives and free relatives through the generic mechanism follows the
substrate, not K&L's text (they explicitly defer directives to later work and
never discuss free relatives). -/

/-- The indefinite containing *any* is interpreted episodically (PS *any*) or generically
(FC *any*). -/
inductive AnyInterpretation where
  | episodic
  | generic
  deriving DecidableEq, Repr

/-- The interpretation of *any* in a licensing context is projected from the licensing
mechanism, and is generic exactly when the substrate classifies the context as licensed by the
generic indefinite. -/
noncomputable def interpretationOf (c : LicensingContext) : AnyInterpretation :=
  match c.licenser.mechanism with
  | .genericIndefinite => .generic
  | _ => .episodic

theorem interpretationOf_eq_generic_iff (c : LicensingContext) :
    interpretationOf c = .generic ↔ c.licenser.mechanism = .genericIndefinite := by
  cases h : c.licenser.mechanism <;> simp only [interpretationOf, h] <;> decide

/-! ### Vague restrictions and precisifications

K&L §4.1: *every owl* is **domain precise** — context determines a unique
domain — while generic *an owl* is **domain vague**: the normalcy restriction
is inherently underspecified, and different precisifications yield different
domains. This is what lets generics tolerate exceptions ("a poodle gives live
birth" survives male poodles). The `Set`-based notions are stated locally
because the supervaluation substrate (`SignType.supervaluation`) is
`Finset`-based for computability; the finite case is below. -/

/-- A vague restriction ⟨v₀, V⟩ (K&L §4.1) is a precise part, the properties known to hold,
together with its consistent completions, each extending the precise part, which is itself a
minimal precisification. -/
structure VagueRestriction (Property : Type*) where
  /-- The precise part holds the properties definitely in the restriction. -/
  precise : Set Property
  /-- The consistent ways to complete the restriction. -/
  precisifications : Set (Set Property)
  /-- Every precisification extends the precise part. -/
  extends_precise : ∀ v ∈ precisifications, precise ⊆ v
  /-- The precise part is itself a (minimal) precisification. -/
  precise_mem : precise ∈ precisifications

/-- The domain induced by a property set is the set of entities satisfying every property. -/
def domainOf {Property Entity : Type*} (props : Set Property)
    (apply : Property → Set Entity) : Set Entity :=
  {e | ∀ P ∈ props, e ∈ apply P}

/-- A restriction is domain precise (K&L (164)) when every precisification determines the same
domain as the precise part. -/
def isDomainPrecise {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity) : Prop :=
  ∀ v ∈ X.precisifications, domainOf v apply = domainOf X.precise apply

/-- A restriction is domain vague when it is not domain precise, so that some precisifications
yield different domains. -/
def isDomainVague {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity) : Prop :=
  ¬isDomainPrecise X apply

theorem isDomainPrecise_of_forall_eq {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (h : ∀ v ∈ X.precisifications, v = X.precise) :
    isDomainPrecise X apply :=
  fun v hv ↦ by rw [h v hv]

/-- Widening along a dimension (K&L (174)) removes the properties on the dimension from the
precise part and from every precisification. -/
def widenAlong {Property : Type*} (X : VagueRestriction Property)
    (onDimension : Property → Prop) : VagueRestriction Property where
  precise := {P ∈ X.precise | ¬onDimension P}
  precisifications := (fun v ↦ {P ∈ v | ¬onDimension P}) '' X.precisifications
  extends_precise := by
    rintro v' ⟨v, hv, rfl⟩ P ⟨hPprec, hPnot⟩
    exact ⟨X.extends_precise v hv hPprec, hPnot⟩
  precise_mem := ⟨X.precise, X.precise_mem, rfl⟩

theorem widenAlong_weakens_precise {Property : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop) :
    (widenAlong X onDimension).precise ⊆ X.precise :=
  fun _ ⟨h, _⟩ ↦ h

-- §3.5.3
theorem widenAlong_expands_domain {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    (apply : Property → Set Entity) :
    domainOf X.precise apply ⊆
    domainOf (widenAlong X onDimension).precise apply :=
  fun _ he P ⟨hPprec, _⟩ ↦ he P hPprec

/-! ### Dimensional universality

K&L (175)–(177): after widening along a dimension {P, ¬P}, no entity is
excluded on the basis of that dimension, so the quantifier is universal with
respect to it. *Any CN* is dimensionally universal; generic *a CN* is not.
Since *almost* requires a domain-precise universal or a dimensionally
universal NP, this derives *almost any owl* vs ungrammatical *almost an owl*
(§4.3). -/

/-- A restriction is universal with respect to a dimension (K&L (175)) when, after widening along
the dimension, every entity in the base denotation is in the domain. -/
def universalWrtDimension {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    (apply : Property → Set Entity) (baseDenotation : Set Entity) : Prop :=
  baseDenotation ⊆ domainOf (widenAlong X onDimension).precise apply

/-- A dimension is non-trivial on a base set (K&L (176)) when some entity satisfies a property on
the dimension and some entity fails one. -/
def nonTrivialDimension {Property Entity : Type*}
    (onDimension : Property → Prop) (apply : Property → Set Entity)
    (baseDenotation : Set Entity) : Prop :=
  (∃ P, onDimension P ∧ ∃ e ∈ baseDenotation, e ∈ apply P) ∧
  (∃ P, onDimension P ∧ ∃ e ∈ baseDenotation, e ∉ apply P)

/-- A restriction is dimensionally universal (K&L (177)) when it is universal with respect to some
non-trivial dimension. -/
def dimensionallyUniversal {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (baseDenotation : Set Entity) : Prop :=
  ∃ onDimension : Property → Prop,
    nonTrivialDimension onDimension apply baseDenotation ∧
    universalWrtDimension X onDimension apply baseDenotation

/-- *Any CN* is dimensionally universal (K&L §4.3), since widening along a non-trivial dimension
yields universality with respect to that dimension. -/
theorem any_cn_dimensionally_universal {Property Entity : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    (apply : Property → Set Entity) (baseDenotation : Set Entity)
    (hNT : nonTrivialDimension onDimension apply baseDenotation)
    (hBase : baseDenotation ⊆ domainOf {P ∈ X.precise | ¬onDimension P} apply) :
    dimensionallyUniversal (widenAlong X onDimension) apply baseDenotation :=
  ⟨onDimension, hNT, fun _ he P ⟨⟨hPprec, hPnot⟩, _⟩ ↦ hBase he P ⟨hPprec, hPnot⟩⟩

theorem widenAlong_precise_eq_empty {Property : Type*}
    (X : VagueRestriction Property) (onDimension : Property → Prop)
    (hAllOnDim : ∀ P ∈ X.precise, onDimension P) :
    (widenAlong X onDimension).precise = ∅ := by
  ext P
  simp only [widenAlong, Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false]
  intro ⟨hP, hNot⟩
  exact hNot (hAllOnDim P hP)

/-! ### Generic quantification as vague universality

K&L §4.1.1: a generic is a universal restricted by a vague set of properties, "An owl hunts mice"
being ∀ ↾ X_owl(Owl)(Hunts mice), (158) and (159), which (161) glosses as *all normal owls hunt
mice*, with what counts as normal inherently vague. The vague set plays the part of GEN's
normality: a precisification induces a `Genericity.Normality`, whose normal owls are the owls
with its properties, and the generic under a precisification is GEN under that normality.
Exception tolerance is the freedom to choose another precisification. -/

/-- Under the normality a precisification induces (161), the normal instances of a restrictor are
those with every property of the precisification. -/
def precisificationNormality {Property Entity : Type*} (apply : Property → Set Entity) :
    Genericity.Normality (Set Property) Entity :=
  .ofAccess (domainOf · apply)

/-- Under one precisification, the generic (159) holds when every instance of the restrictor with
the precisified properties satisfies the scope, GEN under the normality the precisification
induces. -/
def genericTrue {Property Entity : Type*} (apply : Property → Set Entity) (R : Set Entity)
    (scope : Entity → Prop) (v : Set Property) : Prop :=
  v ∈ (precisificationNormality apply).gen R {e | scope e}

/-- A generic is supervaluationistically true when it is true under every precisification. -/
def genericSuperTrue {Property Entity : Type*} (X : VagueRestriction Property)
    (apply : Property → Set Entity) (R : Set Entity) (scope : Entity → Prop) : Prop :=
  ∀ v ∈ X.precisifications, genericTrue apply R scope v

/-- A generic is subvaluationistically true when it is true under some precisification, the
exception-tolerant reading. -/
def genericSubTrue {Property Entity : Type*} (X : VagueRestriction Property)
    (apply : Property → Set Entity) (R : Set Entity) (scope : Entity → Prop) : Prop :=
  ∃ v ∈ X.precisifications, genericTrue apply R scope v

/-- Domain vagueness yields two precisifications with different domains —
the room generics need for legitimate exceptions. -/
theorem domain_vague_allows_exceptions {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (hVague : isDomainVague X apply) :
    ∃ v₁ ∈ X.precisifications, ∃ v₂ ∈ X.precisifications,
      domainOf v₁ apply ≠ domainOf v₂ apply := by
  unfold isDomainVague isDomainPrecise at hVague
  push Not at hVague
  obtain ⟨v, hv, hne⟩ := hVague
  exact ⟨v, hv, X.precise, X.precise_mem, hne⟩

theorem domain_vagueness_explains_gen_exceptions {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (R : Set Entity) (scope : Entity → Prop) (hVague : isDomainVague X apply)
    (hSub : genericSubTrue X apply R scope) :
    ∃ v₁ ∈ X.precisifications, ∃ v₂ ∈ X.precisifications,
      domainOf v₁ apply ≠ domainOf v₂ apply ∧
      genericTrue apply R scope v₁ := by
  obtain ⟨v₁, hv₁m, v₂, hv₂m, hne⟩ := domain_vague_allows_exceptions X apply hVague
  obtain ⟨vg, hvgm, hvgt⟩ := hSub
  by_cases h : domainOf vg apply = domainOf v₁ apply
  · exact ⟨vg, hvgm, v₂, hv₂m, by rw [h]; exact hne, hvgt⟩
  · exact ⟨vg, hvgm, v₁, hv₁m, h, hvgt⟩

/-! ### Grounding in Fine 1975 supervaluation

When the precisification set is finite, K&L's truth notions are
[fine-1975]'s: `genericSuperTrue` is super-truth on the induced
specification space, and the exception-tolerance zone — sub-true but not
super-true — is exactly Fine's borderline status, supervaluation value `0`. "A poodle gives
live birth" is Fine-indefinite and K&L-assertable. -/

theorem genericSuperTrue_iff_superTrue {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (R : Set Entity) (scope : Entity → Prop) [DecidablePred (genericTrue apply R scope)]
    (V : Finset (Set Property)) (hV : ↑V = X.precisifications) :
    genericSuperTrue X apply R scope ↔
      SignType.supervaluation V (genericTrue apply R scope) = 1 := by
  rw [SignType.supervaluation_eq_one_iff]
  simp only [genericSuperTrue, ← hV, Finset.mem_coe]

/-- K&L's exception-tolerance zone is Fine's borderline zone. A generic that is
subvaluationistically but not supervaluationistically true is exactly one whose supervaluation
status is indefinite, assertable for K&L and borderline for [fine-1975]. -/
theorem genericSubTrue_not_superTrue_iff_indet {Property Entity : Type*}
    (X : VagueRestriction Property) (apply : Property → Set Entity)
    (R : Set Entity) (scope : Entity → Prop) [DecidablePred (genericTrue apply R scope)]
    (V : Finset (Set Property)) (hV : ↑V = X.precisifications) :
    genericSubTrue X apply R scope ∧ ¬genericSuperTrue X apply R scope ↔
      SignType.supervaluation V (genericTrue apply R scope) = 0 := by
  rw [SignType.supervaluation_eq_zero_iff]
  simp only [genericSubTrue, genericSuperTrue, ← hV, Finset.mem_coe, not_forall, exists_prop]

/-! ### The *almost* test

K&L: *almost* modifies domain-precise true universal quantifiers (∀ or ¬∃)
and, after §4.3, dimensionally universal NPs. *Some owl* is domain precise
(K&L p. 412 group it with *every owl* and *no owl*) but not universal, so
*almost some owl* is out; generic *an owl* has universal force but a vague
domain; *any owl* is rescued by dimensional universality. -/

/-- The domain precision of a noun phrase's restriction, Section 4.1.2. -/
inductive DomainPrecision
  | precise
  | vague
  deriving DecidableEq, Repr

/-- An *almost* row records the noun phrase, its precision, whether it is a true universal and
whether it is dimensionally universal, and the judgment. -/
structure AlmostRow where
  precision : DomainPrecision
  universal : Bool
  dimUniversal : Bool
  ok : Bool
  deriving DecidableEq

/-- An *almost* row from the paper's features. -/
def AlmostRow.ofDatum (e : Datum) : Option AlmostRow := do
  let p ← match e.feature? "precision" with
    | some "precise" => some DomainPrecision.precise
    | some "vague" => some DomainPrecision.vague
    | _ => none
  let u ← e.feature? "universal"
  let d ← e.feature? "dimensionally_universal"
  some ⟨p, u == "yes", d == "yes", e.judgment = .acceptable⟩

/-- The *almost* data of Sections 4.1.1 and 4.3. -/
def almostRows : List AlmostRow := Examples.all.filterMap AlmostRow.ofDatum

/-- *Almost* modifies a domain-precise true universal or a dimensionally universal noun phrase,
such as *every owl*, *no owl* and *any owl*, but not *some owl* nor generic *an owl*. -/
theorem almost_rows :
    ∀ r ∈ almostRows, r.ok = true ↔ (r.universal = true ∧ r.precision = .precise) ∨
      r.dimUniversal = true := by
  decide

/-! ### The licensing data -/

/-- A licensing row records the context at the narrowest operator over *any*, a licensing context
or a local entailment signature, the settle-for-less and metalinguistic-denial readings, and the
judgment. -/
structure Row where
  context : Option LicensingContext
  localSignature : Signature
  settleForLess : Bool
  metalinguistic : Bool
  grammatical : Bool

/-- The licensing context a row names. -/
def contextOf : String → Option LicensingContext
  | "negation" => some .negation
  | "generic" => some .generic
  | "universalRestrictor" => some .universalRestrictor
  | "adversative" => some .adversative
  | "conditionalAntecedent" => some .conditionalAntecedent
  | _ => none

def signatureOf : String → Option Signature
  | "all" => some .all
  | "mono" => some .mono
  | "anti" => some .anti
  | "mult" => some .mult
  | _ => none

/-- A row from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row :=
  match (e.feature? "context").bind contextOf, (e.feature? "local_signature").bind signatureOf with
  | some c, _ => some ⟨some c, .all, e.feature? "settle_for_less" = some "yes",
      e.feature? "metalinguistic_denial" = some "yes", e.judgment = .acceptable⟩
  | none, some σ => some ⟨none, σ, e.feature? "settle_for_less" = some "yes",
      e.feature? "metalinguistic_denial" = some "yes", e.judgment = .acceptable⟩
  | none, none => none

/-- The licensing data of Sections 1 to 3. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- On the paper's own data, *any* is grammatical exactly when its context licenses it, as a
downward-entailing or a generic context, or the local signature is downward entailing, so widening
strengthens, or it is read as settling for less under *glad*, or as a metalinguistic denial under a
negated *because*. -/
theorem rows_agree :
    ∀ r ∈ rows, r.grammatical = true ↔
      (∃ c ∈ r.context, c.licenser.Licenses English.PolarityItems.any) ∨
        r.localSignature.negationStrength ≠ ⊥ ∨ r.settleForLess = true ∨
          r.metalinguistic = true := by
  decide +kernel

end KadmonLandman1993
