module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Basic.Sign.Defs
public import Linglib.Core.Order.AntiAdditive
public import Linglib.Logic.Natural.Relation
public import Linglib.Semantics.Negation.Polarity

/-!
# Projectivity signatures

A map between bounded lattices is *additive* if it preserves `⊔` and `⊤`, *multiplicative* if it
preserves `⊓` and `⊥`, and *anti-additive* or *anti-multiplicative* if it is additive or
multiplicative as a map into the order dual. A projectivity signature names a class of maps: all
maps, the monotone maps and those of them that are additive, multiplicative or both, and the
antitone maps and those of them that are anti-additive, anti-multiplicative or both. There are
nine.

We define the signatures and say when a signature holds of a map. The composition `ψ * φ` of two
signatures holds of every `ψ`-function after a `φ`-function. Under composition the signatures form
a monoid with zero: the identity is the signature `⊕` of the bounded lattice homomorphisms, and
the zero is the signature `•` of all maps. The sign of a signature, `1` for a monotone class, `-1`
for an antitone class and `0` for `•`, is a homomorphism to the three signs.

## Main definitions

* `ProjectivitySignature`: the nine signatures, ordered by refinement.
* `ProjectivitySignature.HoldsFor`: `σ.HoldsFor f` says that `f` has every property `σ` asserts.
* `ProjectivitySignature.compose`: composition of signatures, the multiplication of the monoid.
* `signHom`, `unitsEquiv`: the sign as a homomorphism of monoids with zero, and the invertible
  signatures as the two polarities.

## Main results

* `HoldsFor.comp`: a `ψ`-function after a `φ`-function is a `ψ * φ`-function.
* `holdsFor_comp_left_iff`, `holdsFor_comp_right_iff`: a map composed with an invertible map of
  signature `υ` is a `σ`-function exactly when the map is a `υ⁻¹ * σ`-function or a
  `σ * υ⁻¹`-function.
* `holdsFor_toDual_comp_iff`: a map into the order dual is a `σ`-function exactly when the map is
  a `⊖ * σ`-function.
* `holdsFor_additive_sup`, `holdsFor_additive_top`: the additive maps are closed under pointwise
  joins and contain the constant `⊤`, and likewise for the other three properties.
* `mul_eq_top`: a composite is the signature of all maps only when a factor is.

## Implementation notes

* Icard states the definitions for maps between Boolean lattices. Only the bounded lattice
  structure is used here.
* An additive map is a homomorphism of what Icard calls ∨-1-semilattices, a join-semilattice with
  its top, and a multiplicative map one of ∧-0-semilattices. These pair `⊔` with `⊤` and `⊓` with
  `⊥`, as the hypotheses of mathlib's `Codisjoint.map` and `Disjoint.map` do, and not as
  `SupBotHom` and `InfTopHom` do. The function classes are therefore predicates on a map, with
  constructors from the hom classes; a grammatical operator is asked whether it has them.
* `σ ≤ τ` says that every `σ`-function is a `τ`-function, so the most specific signatures are the
  least and the signature of all maps is the top.
* Composition is computed from a rule on pairs of properties and is not tabulated: `ψ * φ` asserts
  what the rule derives from a property of `ψ` and one of `φ`. It is the least signature holding
  of all composites, `NaturalLogic.ProjectivitySignature.isLeast_compose`, so that
  `antiAdd * antiAdd = mono`, `antiMult * mult = antiMult` and `antiAddMult * antiMult = mult`.

## References

* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

/-! ### Projectivity signatures -/

/-- The nine projectivity signatures of [icard-2012] (Definition 1.11), the function classes a
relation can be projected through, from arbitrary (`•`) to anti-morphism (`⊖`). Each but `•`
holds of a function with the *complete* properties of [icard-2012] Definition 1.7, which also fix
the image of `⊥` or `⊤`. -/
inductive ProjectivitySignature where
  /-- An arbitrary function (`•`), projecting every relation but `≡` to `#`. -/
  | all
  /-- A monotone function (`+`, upward entailing). -/
  | mono
  /-- An antitone function (`−`, downward entailing). -/
  | anti
  /-- An additive function, preserving joins and `⊤`; [icard-2012] writes `+` in a diamond. -/
  | additive
  /-- An anti-additive function, turning joins into meets and `⊤` into `⊥`; [icard-2012] writes
  `−` in a diamond. -/
  | antiAdd
  /-- A multiplicative function (`⊞`), preserving meets and `⊥`. -/
  | mult
  /-- An anti-multiplicative function (`⊟`), turning meets into joins and `⊥` into `⊤`. -/
  | antiMult
  /-- A morphism (`⊕`), additive and multiplicative. -/
  | addMult
  /-- An anti-morphism (`⊖`), anti-additive and anti-multiplicative. -/
  | antiAddMult
  deriving DecidableEq, Fintype, Repr

namespace ProjectivitySignature

/-- The six properties of maps that a signature can assert. -/
inductive Property where
  /-- Preserves `≤`. -/
  | monotone
  /-- Reverses `≤`. -/
  | antitone
  /-- Preserves `⊔` and `⊤`. -/
  | additive
  /-- Preserves `⊓` and `⊥`. -/
  | multiplicative
  /-- Sends `⊔` to `⊓` and `⊤` to `⊥`. -/
  | antiAdditive
  /-- Sends `⊓` to `⊔` and `⊥` to `⊤`. -/
  | antiMultiplicative
  deriving DecidableEq, Fintype, Repr

/-- The properties a signature asserts. -/
def properties : ProjectivitySignature → Finset Property
  | .all => ∅
  | .mono => {.monotone}
  | .anti => {.antitone}
  | .additive => {.monotone, .additive}
  | .mult => {.monotone, .multiplicative}
  | .antiAdd => {.antitone, .antiAdditive}
  | .antiMult => {.antitone, .antiMultiplicative}
  | .addMult => {.monotone, .additive, .multiplicative}
  | .antiAddMult => {.antitone, .antiAdditive, .antiMultiplicative}

theorem properties_injective : Function.Injective properties := by decide

/-- The first signature, from the most specific up to `•`, all of whose properties satisfy `P`. -/
def ofProperties (P : Property → Prop) [DecidablePred P] : ProjectivitySignature :=
  ([addMult, antiAddMult, additive, mult, antiAdd, antiMult, mono, anti].find?
    (fun σ ↦ ∀ p ∈ σ.properties, P p)).getD all

/-- The refinement order ([icard-2012]'s ≼): `σ ≤ τ` when the properties of `τ` are among those of
`σ`, so that every σ-function is a τ-function. -/
instance : PartialOrder ProjectivitySignature :=
  .lift (fun σ ↦ OrderDual.toDual (properties σ))
    (OrderDual.toDual.injective.comp properties_injective)

theorem le_iff {σ τ : ProjectivitySignature} :
    σ ≤ τ ↔ properties τ ⊆ properties σ := Iff.rfl

instance : DecidableLE ProjectivitySignature := fun _ _ ↦
  decidable_of_iff _ le_iff.symm

instance : DecidableLT ProjectivitySignature := decidableLTOfDecidableLE

@[simp] theorem ofProperties_mem_properties (σ : ProjectivitySignature) :
    ofProperties (· ∈ σ.properties) = σ := by
  revert σ; decide

instance : OrderTop ProjectivitySignature where
  top := .all
  le_top _ := le_iff.mpr (Finset.empty_subset _)

/-- The properties a signature asserts, as an order embedding into the sets of properties under
reverse inclusion. -/
def propertiesOrderEmbedding : ProjectivitySignature ↪o (Finset Property)ᵒᵈ where
  toFun σ := OrderDual.toDual σ.properties
  inj' := OrderDual.toDual.injective.comp properties_injective
  map_rel_iff' := Iff.rfl

@[simp] theorem propertiesOrderEmbedding_apply (σ : ProjectivitySignature) :
    propertiesOrderEmbedding σ = OrderDual.toDual σ.properties := rfl

/-- The property that a function with property `p` after a function with property `q` has, when the
two determine one. -/
def Property.compose : Property → Property → Option Property
  | .monotone, .monotone | .antitone, .antitone => some .monotone
  | .monotone, .antitone | .antitone, .monotone => some .antitone
  | .additive, .additive | .antiMultiplicative, .antiAdditive => some .additive
  | .multiplicative, .multiplicative | .antiAdditive, .antiMultiplicative => some .multiplicative
  | .antiAdditive, .additive | .multiplicative, .antiAdditive => some .antiAdditive
  | .antiMultiplicative, .multiplicative | .additive, .antiMultiplicative =>
      some .antiMultiplicative
  | _, _ => none

/-- The property rule for composition is associative. -/
theorem Property.compose_assoc : ∀ p q r : Property,
    (p.compose q).bind (·.compose r) = (q.compose r).bind (p.compose ·) := by
  decide

/-! ### Composition -/

/-- The composition `compose ψ φ` of projectivity signatures ([icard-2012], Definition 2.6 and
Lemma 2.7), `φ` inner and `ψ` outer, is the signature asserting what the property rule gives for
each property of `ψ` and of `φ`. -/
def compose (ψ φ : ProjectivitySignature) : ProjectivitySignature :=
  ofProperties fun r ↦ ∃ p ∈ ψ.properties, ∃ q ∈ φ.properties, p.compose q = some r

instance : Mul ProjectivitySignature where mul := compose
instance : One ProjectivitySignature where one := .addMult

theorem mem_properties_mul {ψ φ : ProjectivitySignature} {r : Property} :
    r ∈ (ψ * φ).properties ↔ ∃ p ∈ ψ.properties, ∃ q ∈ φ.properties, p.compose q = some r := by
  revert ψ φ r
  decide

/-- `•` absorbs on the left ([icard-2012] p. 716). -/
@[simp] theorem top_mul (σ : ProjectivitySignature) : ⊤ * σ = ⊤ := by cases σ <;> rfl

/-- `•` absorbs on the right ([icard-2012] p. 716). -/
@[simp] theorem mul_top (σ : ProjectivitySignature) : σ * ⊤ = ⊤ := by cases σ <;> rfl

/-- The signatures form a monoid with zero under composition ([icard-2012] Lemma 2.7), with identity
`⊕` and zero `•`. It is not commutative: `antiMult * antiAdd = additive` but
`antiAdd * antiMult = mult`. -/
instance : MonoidWithZero ProjectivitySignature where
  mul_assoc ψ φ χ := properties_injective <| Finset.ext fun _ ↦ by
    simp only [mem_properties_mul]
    exact exists_bind_comm Property.compose_assoc
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  zero := ⊤
  zero_mul := top_mul
  mul_zero := mul_top

@[simp] theorem zero_eq_top : (0 : ProjectivitySignature) = ⊤ := rfl

/-- Composition with a more specific signature is more specific. -/
instance : MulLeftMono ProjectivitySignature where
  elim ψ _ _ h := le_iff.2 fun _ hr ↦ by
    obtain ⟨p, hp, q, hq, hpq⟩ := mem_properties_mul.1 hr
    exact mem_properties_mul.2 ⟨p, hp, q, le_iff.1 h hq, hpq⟩

instance : MulRightMono ProjectivitySignature where
  elim φ _ _ h := le_iff.2 fun _ hr ↦ by
    obtain ⟨p, hp, q, hq, hpq⟩ := mem_properties_mul.1 hr
    exact mem_properties_mul.2 ⟨p, le_iff.1 h hp, q, hq, hpq⟩

/-! ### Signs and polarities -/

/-- The sign of a signature is its marking in the Monotonicity Calculus: `1` if its class is
monotone, `-1` if it is antitone, and `0` otherwise, as for a non-monotone context such as
*exactly n* or an arbitrary one. -/
def sign (φ : ProjectivitySignature) : SignType :=
  if .monotone ∈ φ.properties then 1 else if .antitone ∈ φ.properties then -1 else 0

/-- The signatures of positive sign are those refining `+`. -/
theorem sign_eq_one_iff {φ : ProjectivitySignature} : φ.sign = 1 ↔ φ ≤ mono := by
  revert φ; decide

/-- The signatures of negative sign are those refining `−`. -/
theorem sign_eq_neg_one_iff {φ : ProjectivitySignature} : φ.sign = -1 ↔ φ ≤ anti := by
  revert φ; decide

/-- Only `•` has no direction. -/
@[simp] theorem sign_eq_zero_iff {φ : ProjectivitySignature} : φ.sign = 0 ↔ φ = ⊤ := by
  revert φ; decide

@[simp] theorem sign_one : (1 : ProjectivitySignature).sign = 1 := rfl

@[simp] theorem sign_top : (⊤ : ProjectivitySignature).sign = 0 := rfl

@[simp] theorem sign_mul (φ ψ : ProjectivitySignature) : (φ * ψ).sign = φ.sign * ψ.sign := by
  revert φ ψ; decide

/-- `sign` as a homomorphism of monoids with zero: the projectivity calculus composes its markings
as the Monotonicity Calculus composes `+` and `−` ([icard-2012] p. 716). -/
def signHom : ProjectivitySignature →*₀ SignType where
  toFun := sign
  map_zero' := rfl
  map_one' := rfl
  map_mul' := sign_mul

@[simp] theorem coe_signHom : ⇑signHom = sign := rfl

/-- A composite of signatures with a direction has a direction. -/
instance : NoZeroDivisors ProjectivitySignature where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    simpa using congrArg sign h

/-- A composite is `•` only when a factor is. -/
@[simp] theorem mul_eq_top {φ ψ : ProjectivitySignature} : φ * ψ = ⊤ ↔ φ = ⊤ ∨ ψ = ⊤ :=
  mul_eq_zero

/-- A polarity as a signature, the positive one the morphism signature `⊕` and the negative one
the anti-morphism `⊖`. -/
def ofPolarity : Polarity →* ProjectivitySignature := Polarity.lift ⟨.antiAddMult, rfl⟩

@[simp] theorem ofPolarity_positive : ofPolarity .positive = addMult := rfl

@[simp] theorem ofPolarity_negative : ofPolarity .negative = antiAddMult := rfl

@[simp] theorem sign_ofPolarity (p : Polarity) : (ofPolarity p).sign = p := by
  cases p <;> decide

/-- Only `⊕` and `⊖` are invertible, each its own inverse ([icard-2012] p. 716). -/
theorem isUnit_iff {σ : ProjectivitySignature} : IsUnit σ ↔ σ ∈ Set.range ofPolarity := by
  rw [isUnit_iff_exists, Set.mem_range]
  revert σ
  decide

/-- The invertible signatures are the two polarities. -/
def unitsEquiv : Polarity ≃* ProjectivitySignatureˣ where
  toFun := ofPolarity.toHomUnits
  invFun u := if u.val.sign = 1 then .positive else .negative
  left_inv p := by cases p <;> rfl
  right_inv u := Units.ext <| by
    obtain ⟨p, hp⟩ := isUnit_iff.1 u.isUnit
    change ofPolarity (if u.val.sign = 1 then .positive else .negative) = u.val
    rw [← hp]
    cases p <;> rfl
  map_mul' := map_mul _

@[simp] theorem val_unitsEquiv (p : Polarity) :
    (unitsEquiv p : ProjectivitySignature) = ofPolarity p := rfl

/-! ### The function class of a signature -/

section HoldsFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]

/-- `p.HoldsFor f` says that the map `f` has the property `p`. -/
def Property.HoldsFor : Property → (α → β) → Prop
  | .monotone => Monotone
  | .antitone => Antitone
  | .additive => fun f ↦ (∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤
  | .multiplicative => fun f ↦ (∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥
  | .antiAdditive => fun f ↦ IsAntiAdditive f ∧ f ⊤ = ⊥
  | .antiMultiplicative => fun f ↦ IsAntiMultiplicative f ∧ f ⊥ = ⊤

/-- `σ.HoldsFor f` says that `f` has every property `σ` asserts; [icard-2012] calls such an `f` a
σ-function. -/
def HoldsFor (σ : ProjectivitySignature) (f : α → β) : Prop :=
  ∀ p ∈ σ.properties, p.HoldsFor f

theorem HoldsFor.of_le {σ τ : ProjectivitySignature} {f : α → β}
    (h : σ.HoldsFor f) (hστ : σ ≤ τ) : τ.HoldsFor f :=
  fun p hp ↦ h p (le_iff.mp hστ hp)

/-! #### The nine classes -/

@[simp] theorem holdsFor_all (f : α → β) : HoldsFor .all f :=
  fun _ hp ↦ absurd hp (Finset.notMem_empty _)

@[simp] theorem holdsFor_top (f : α → β) : HoldsFor ⊤ f := holdsFor_all f

theorem holdsFor_mono_iff {f : α → β} : HoldsFor .mono f ↔ Monotone f := by
  simp [HoldsFor, properties, Property.HoldsFor]

theorem holdsFor_anti_iff {f : α → β} : HoldsFor .anti f ↔ Antitone f := by
  simp [HoldsFor, properties, Property.HoldsFor]

theorem holdsFor_additive_iff {f : α → β} :
    HoldsFor .additive f ↔ (∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤ := by
  simp only [HoldsFor, properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨.of_map_sup h.1, h⟩⟩

theorem holdsFor_mult_iff {f : α → β} :
    HoldsFor .mult f ↔ (∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥ := by
  simp only [HoldsFor, properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨.of_map_inf h.1, h⟩⟩

theorem holdsFor_antiAdd_iff {f : α → β} :
    HoldsFor .antiAdd f ↔ IsAntiAdditive f ∧ f ⊤ = ⊥ := by
  simp only [HoldsFor, properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.antitone, h⟩⟩

theorem holdsFor_antiMult_iff {f : α → β} :
    HoldsFor .antiMult f ↔ IsAntiMultiplicative f ∧ f ⊥ = ⊤ := by
  simp only [HoldsFor, properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.antitone, h⟩⟩

theorem holdsFor_addMult_iff {f : α → β} :
    HoldsFor .addMult f ↔
      ((∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤) ∧ (∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥ := by
  simp only [HoldsFor, properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨.of_map_sup h.1.1, h⟩⟩

theorem holdsFor_antiAddMult_iff {f : α → β} :
    HoldsFor .antiAddMult f ↔
      (IsAntiAdditive f ∧ f ⊤ = ⊥) ∧ IsAntiMultiplicative f ∧ f ⊥ = ⊤ := by
  simp only [HoldsFor, properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.1.antitone, h⟩⟩

/-! #### Homomorphisms -/

/-- A homomorphism of join-semilattices with top is additive. -/
theorem holdsFor_additive_of_supHomClass {F : Type*} [FunLike F α β] [SupHomClass F α β]
    [TopHomClass F α β] (f : F) : HoldsFor .additive f :=
  holdsFor_additive_iff.2 ⟨map_sup f, map_top f⟩

/-- A homomorphism of meet-semilattices with bottom is multiplicative. -/
theorem holdsFor_mult_of_infHomClass {F : Type*} [FunLike F α β] [InfHomClass F α β]
    [BotHomClass F α β] (f : F) : HoldsFor .mult f :=
  holdsFor_mult_iff.2 ⟨map_inf f, map_bot f⟩

/-- A bounded lattice homomorphism is a morphism. -/
theorem holdsFor_addMult_of_boundedLatticeHomClass {F : Type*} [FunLike F α β]
    [BoundedLatticeHomClass F α β] (f : F) : HoldsFor .addMult f :=
  holdsFor_addMult_iff.2 ⟨⟨map_sup f, map_top f⟩, map_inf f, map_bot f⟩

/-- A morphism as a bounded lattice homomorphism. -/
def HoldsFor.toBoundedLatticeHom {f : α → β} (h : HoldsFor .addMult f) : BoundedLatticeHom α β where
  toFun := f
  map_sup' := (holdsFor_addMult_iff.1 h).1.1
  map_inf' := (holdsFor_addMult_iff.1 h).2.1
  map_top' := (holdsFor_addMult_iff.1 h).1.2
  map_bot' := (holdsFor_addMult_iff.1 h).2.2

@[simp] theorem HoldsFor.coe_toBoundedLatticeHom {f : α → β} (h : HoldsFor .addMult f) :
    ⇑h.toBoundedLatticeHom = f := rfl

theorem holdsFor_addMult_id : HoldsFor .addMult (id : α → α) :=
  holdsFor_addMult_of_boundedLatticeHomClass (BoundedLatticeHom.id α)

theorem holdsFor_antiAddMult_compl {γ : Type*} [BooleanAlgebra γ] :
    HoldsFor .antiAddMult (compl : γ → γ) :=
  holdsFor_antiAddMult_iff.2
    ⟨⟨isAntiAdditive_compl, compl_top⟩, isAntiMultiplicative_compl, compl_bot⟩

/-- Passing to the order dual is an anti-morphism. -/
theorem holdsFor_antiAddMult_toDual : HoldsFor .antiAddMult (OrderDual.toDual : α → αᵒᵈ) :=
  holdsFor_antiAddMult_iff.2 ⟨⟨fun _ _ ↦ rfl, rfl⟩, fun _ _ ↦ rfl, rfl⟩

/-- Returning from the order dual is an anti-morphism. -/
theorem holdsFor_antiAddMult_ofDual : HoldsFor .antiAddMult (OrderDual.ofDual : αᵒᵈ → α) :=
  holdsFor_antiAddMult_iff.2 ⟨⟨fun _ _ ↦ rfl, rfl⟩, fun _ _ ↦ rfl, rfl⟩

/-! #### Composition -/

section Comp

variable {γ : Type*} [Lattice γ] [BoundedOrder γ] {σ υ υ' : ProjectivitySignature}

/-- The property rule for composition is sound: a function with property `p` after one with
property `q` has the property `Property.compose` says. -/
theorem Property.HoldsFor.compose {p q r : Property} {f : β → γ} {g : α → β}
    (h : p.compose q = some r) (hf : p.HoldsFor f) (hg : q.HoldsFor g) : r.HoldsFor (f ∘ g) := by
  cases p <;> cases q <;> simp only [Property.compose, reduceCtorEq,
    Option.some.injEq] at h <;> subst h <;>
    simp only [Property.HoldsFor, IsAntiAdditive, IsAntiMultiplicative] at hf hg ⊢
  all_goals first
    | exact Monotone.comp hf hg
    | exact Antitone.comp hf hg
    | exact Monotone.comp_antitone hf hg
    | exact Antitone.comp_monotone hf hg
    | exact ⟨fun x y ↦ by simp only [Function.comp_apply, hg.1, hf.1],
        by simp only [Function.comp_apply, hg.2, hf.2]⟩

/-- A ψ-function after a φ-function is a `ψ * φ`-function, over any bounded lattices: the function
classes compose as `compose` says ([icard-2012] Definition 2.6 and Lemma 2.7). -/
theorem HoldsFor.comp {ψ φ : ProjectivitySignature} {f : β → γ} {g : α → β}
    (hf : ψ.HoldsFor f) (hg : φ.HoldsFor g) : (ψ * φ).HoldsFor (f ∘ g) := fun _ hr ↦ by
  obtain ⟨p, hp, q, hq, h⟩ := mem_properties_mul.1 hr
  exact (hf p hp).compose h (hg q hq)

/-- If `e` is a `υ`-function with a right inverse `e'` that is a `υ'`-function, and `υ' * υ = 1`,
then a map after `e` is a `σ`-function exactly when the map is a `σ * υ'`-function. -/
theorem holdsFor_comp_right_iff (h : υ' * υ = 1) {e : α → β} {e' : β → α} (he : υ.HoldsFor e)
    (he' : υ'.HoldsFor e') (hee' : Function.LeftInverse e e') {f : β → γ} :
    σ.HoldsFor (f ∘ e) ↔ (σ * υ').HoldsFor f := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · simpa [Function.comp_assoc, hee'.comp_eq_id] using hf.comp he'
  · simpa [mul_assoc, h] using hf.comp he

/-- If `e` is a `υ`-function with a left inverse `e'` that is a `υ'`-function, and `υ * υ' = 1`,
then `e` after a map is a `σ`-function exactly when the map is a `υ' * σ`-function. -/
theorem holdsFor_comp_left_iff (h : υ * υ' = 1) {e : β → γ} {e' : γ → β} (he : υ.HoldsFor e)
    (he' : υ'.HoldsFor e') (hee' : Function.LeftInverse e' e) {f : α → β} :
    σ.HoldsFor (e ∘ f) ↔ (υ' * σ).HoldsFor f := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · simpa [← Function.comp_assoc, hee'.comp_eq_id] using he'.comp hf
  · simpa [← mul_assoc, h] using he.comp hf

end Comp

/-! #### Duality

The anti-additive maps into a lattice are the additive maps into its order dual, and likewise for
the other classes ([icard-2012] Lemma 1.10): dualizing the target of a map multiplies its
signature by `⊖` on the left, and dualizing the source multiplies it on the right. -/

section Dual

variable {σ : ProjectivitySignature}

theorem holdsFor_toDual_comp_iff {f : α → β} :
    σ.HoldsFor (OrderDual.toDual ∘ f) ↔ (antiAddMult * σ).HoldsFor f :=
  holdsFor_comp_left_iff rfl holdsFor_antiAddMult_toDual holdsFor_antiAddMult_ofDual fun _ ↦ rfl

theorem holdsFor_ofDual_comp_iff {f : α → βᵒᵈ} :
    σ.HoldsFor (OrderDual.ofDual ∘ f) ↔ (antiAddMult * σ).HoldsFor f :=
  holdsFor_comp_left_iff rfl holdsFor_antiAddMult_ofDual holdsFor_antiAddMult_toDual fun _ ↦ rfl

theorem holdsFor_comp_toDual_iff {f : αᵒᵈ → β} :
    σ.HoldsFor (f ∘ OrderDual.toDual) ↔ (σ * antiAddMult).HoldsFor f :=
  holdsFor_comp_right_iff rfl holdsFor_antiAddMult_toDual holdsFor_antiAddMult_ofDual fun _ ↦ rfl

theorem holdsFor_comp_ofDual_iff {f : α → β} :
    σ.HoldsFor (f ∘ OrderDual.ofDual) ↔ (σ * antiAddMult).HoldsFor f :=
  holdsFor_comp_right_iff rfl holdsFor_antiAddMult_ofDual holdsFor_antiAddMult_toDual fun _ ↦ rfl

/-- A bounded lattice homomorphism into the order dual is an anti-morphism. -/
theorem holdsFor_antiAddMult_of_boundedLatticeHomClass {F : Type*} [FunLike F α βᵒᵈ]
    [BoundedLatticeHomClass F α βᵒᵈ] (f : F) : HoldsFor .antiAddMult (OrderDual.ofDual ∘ f) :=
  holdsFor_ofDual_comp_iff.2 (holdsFor_addMult_of_boundedLatticeHomClass f)

/-- A map after complementation is a σ-function exactly when the map is a `σ * ⊖`-function. -/
theorem holdsFor_comp_compl_iff {γ : Type*} [BooleanAlgebra γ] {g : γ → β} :
    σ.HoldsFor (g ∘ compl) ↔ (σ * .antiAddMult).HoldsFor g :=
  holdsFor_comp_right_iff rfl holdsFor_antiAddMult_compl holdsFor_antiAddMult_compl compl_compl

/-- Complementation after a map is a σ-function exactly when the map is a `⊖ * σ`-function. -/
theorem holdsFor_compl_comp_iff {γ : Type*} [BooleanAlgebra γ] {f : α → γ} :
    σ.HoldsFor (compl ∘ f) ↔ (antiAddMult * σ).HoldsFor f :=
  holdsFor_comp_left_iff rfl holdsFor_antiAddMult_compl holdsFor_antiAddMult_compl compl_compl

end Dual

/-! #### Signs -/

/-- A function in the class of a signature of positive sign is monotone. -/
theorem HoldsFor.monotone_of_sign_eq_one {σ : ProjectivitySignature} {f : α → β}
    (h : σ.HoldsFor f) (hs : σ.sign = 1) : Monotone f :=
  holdsFor_mono_iff.1 (h.of_le (sign_eq_one_iff.1 hs))

/-- A function in the class of a signature of negative sign is antitone. -/
theorem HoldsFor.antitone_of_sign_eq_neg_one {σ : ProjectivitySignature} {f : α → β}
    (h : σ.HoldsFor f) (hs : σ.sign = -1) : Antitone f :=
  holdsFor_anti_iff.1 (h.of_le (sign_eq_neg_one_iff.1 hs))

/-! #### Pointwise joins and meets

The additive maps are closed under pointwise joins and contain the constant `⊤`, and the
multiplicative maps are closed under pointwise meets and contain the constant `⊥`; the
anti-additive and anti-multiplicative maps are so as maps into the order dual ([icard-2012]
Lemma 1.12). -/

theorem holdsFor_additive_sup {f g : α → β} (hf : HoldsFor .additive f)
    (hg : HoldsFor .additive g) : HoldsFor .additive (f ⊔ g) := by
  rw [holdsFor_additive_iff] at hf hg ⊢
  exact ⟨fun p q ↦ by simp only [Pi.sup_apply, hf.1, hg.1, sup_sup_sup_comm],
    by simp only [Pi.sup_apply, hf.2, hg.2, sup_idem]⟩

theorem holdsFor_mult_inf {f g : α → β} (hf : HoldsFor .mult f) (hg : HoldsFor .mult g) :
    HoldsFor .mult (f ⊓ g) := by
  rw [holdsFor_mult_iff] at hf hg ⊢
  exact ⟨fun p q ↦ by simp only [Pi.inf_apply, hf.1, hg.1, inf_inf_inf_comm],
    by simp only [Pi.inf_apply, hf.2, hg.2, inf_idem]⟩

theorem holdsFor_antiAdd_inf {f g : α → β} (hf : HoldsFor .antiAdd f)
    (hg : HoldsFor .antiAdd g) : HoldsFor .antiAdd (f ⊓ g) := by
  rw [holdsFor_antiAdd_iff] at hf hg ⊢
  exact ⟨fun p q ↦ by simp only [Pi.inf_apply, hf.1 p q, hg.1 p q, inf_inf_inf_comm],
    by simp only [Pi.inf_apply, hf.2, hg.2, inf_idem]⟩

theorem holdsFor_antiMult_sup {f g : α → β} (hf : HoldsFor .antiMult f)
    (hg : HoldsFor .antiMult g) : HoldsFor .antiMult (f ⊔ g) := by
  rw [holdsFor_antiMult_iff] at hf hg ⊢
  exact ⟨fun p q ↦ by simp only [Pi.sup_apply, hf.1 p q, hg.1 p q, sup_sup_sup_comm],
    by simp only [Pi.sup_apply, hf.2, hg.2, sup_idem]⟩

/-- The constant `⊤` is additive. -/
theorem holdsFor_additive_top : HoldsFor .additive (⊤ : α → β) :=
  holdsFor_additive_iff.2 ⟨fun _ _ ↦ (sup_idem _).symm, rfl⟩

/-- The constant `⊥` is multiplicative. -/
theorem holdsFor_mult_bot : HoldsFor .mult (⊥ : α → β) :=
  holdsFor_mult_iff.2 ⟨fun _ _ ↦ (inf_idem _).symm, rfl⟩

/-- The constant `⊥` is anti-additive. -/
theorem holdsFor_antiAdd_bot : HoldsFor .antiAdd (⊥ : α → β) :=
  holdsFor_antiAdd_iff.2 ⟨fun _ _ ↦ (inf_idem _).symm, rfl⟩

/-- The constant `⊤` is anti-multiplicative. -/
theorem holdsFor_antiMult_top : HoldsFor .antiMult (⊤ : α → β) :=
  holdsFor_antiMult_iff.2 ⟨fun _ _ ↦ (sup_idem _).symm, rfl⟩

end HoldsFor

section DecidableHoldsFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]
  [Fintype α] [DecidableLE α] [DecidableEq β] [DecidableLE β]

instance Property.decidableHoldsFor :
    ∀ (p : Property) (f : α → β), Decidable (p.HoldsFor f)
  | .monotone, f => decidable_of_iff (∀ a b, a ≤ b → f a ≤ f b) Iff.rfl
  | .antitone, f => decidable_of_iff (∀ a b, a ≤ b → f b ≤ f a) Iff.rfl
  | .additive, f =>
      decidable_of_iff ((∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤) Iff.rfl
  | .multiplicative, f =>
      decidable_of_iff ((∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥) Iff.rfl
  | .antiAdditive, f =>
      decidable_of_iff ((∀ p q, f (p ⊔ q) = f p ⊓ f q) ∧ f ⊤ = ⊥) Iff.rfl
  | .antiMultiplicative, f =>
      decidable_of_iff ((∀ p q, f (p ⊓ q) = f p ⊔ f q) ∧ f ⊥ = ⊤) Iff.rfl

instance decidableHoldsFor (σ : ProjectivitySignature) (f : α → β) :
    Decidable (σ.HoldsFor f) :=
  inferInstanceAs (Decidable (∀ p ∈ σ.properties, p.HoldsFor f))

end DecidableHoldsFor

end ProjectivitySignature

end NaturalLogic
