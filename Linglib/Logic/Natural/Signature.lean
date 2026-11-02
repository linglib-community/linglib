module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Basic.Sign.Defs
public import Linglib.Logic.Natural.Additivity
public import Linglib.Semantics.Negation.Polarity

/-!
# Projectivity signatures

This file defines the function classes of natural logic and the nine projectivity signatures of
Icard that name them. A map between bounded lattices may be monotone or antitone, and additive,
multiplicative, anti-additive or anti-multiplicative with the unit conditions of Icard's complete
properties; a signature asserts some of these properties and [holds of a
map](##NaturalLogic.Signature.HoldsFor) that has them all. Signatures are ordered by refinement,
and composing maps [composes their signatures](##NaturalLogic.Signature.HoldsFor.comp) in a monoid
whose invertible elements are the two polarities and whose sign, the marking of the Monotonicity
Calculus, is multiplicative. The projectivity calculus over the signatures is
`Logic/Natural/Basic.lean`.

## References

* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

/-- Chaining two partial operations gives the same results in either bracketing when the operations
agree pointwise. -/
theorem exists_bind_comm {α β γ δ ζ ε : Type*} {f : α → β → Option γ}
    {g : γ → δ → Option ε} {f' : β → δ → Option ζ} {g' : α → ζ → Option ε}
    (h : ∀ a b d, (f a b).bind (g · d) = (f' b d).bind (g' a ·))
    {s : α → Prop} {t : β → Prop} {u : δ → Prop} {e : ε} :
    (∃ c, (∃ a, s a ∧ ∃ b, t b ∧ f a b = some c) ∧ ∃ d, u d ∧ g c d = some e) ↔
      ∃ a, s a ∧ ∃ z, (∃ b, t b ∧ ∃ d, u d ∧ f' b d = some z) ∧ g' a z = some e := by
  constructor
  · rintro ⟨c, ⟨a, ha, b, hb, hab⟩, d, hd, hcd⟩
    have := h a b d
    rw [hab, Option.bind_some, hcd] at this
    obtain ⟨z, hz, hze⟩ := Option.bind_eq_some_iff.1 this.symm
    exact ⟨a, ha, z, ⟨b, hb, d, hd, hz⟩, hze⟩
  · rintro ⟨a, ha, z, ⟨b, hb, d, hd, hbd⟩, hze⟩
    have := h a b d
    rw [hbd, Option.bind_some, hze] at this
    obtain ⟨c, hc, hce⟩ := Option.bind_eq_some_iff.1 this
    exact ⟨c, ⟨a, ha, b, hb, hc⟩, d, hd, hce⟩

/-! ### Projectivity signatures -/

/-- The nine projectivity signatures of [icard-2012] (Definition 1.11), the function classes a
relation can be projected through, from arbitrary (`•`) to anti-morphism (`⊖`). Each but `•`
holds of a function with the *complete* properties of [icard-2012] Definition 1.7, which also fix
the image of `⊥` or `⊤`. -/
inductive Signature where
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

namespace Signature

/-- The function properties a signature can assert, closed under
implication (an additive function is monotone, so `.additive`'s set contains
`monotone`). -/
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

/-- The properties a signature asserts. Since `≤` is reverse inclusion, `addMult` and
`antiAddMult` are the least elements of their halves and `all` (`•`, no property) is the top. -/
def properties : Signature → Finset Property
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

/-- The most specific signature all of whose properties satisfy `P`, found by trying the
signatures from the most specific up to `•`, which has none. When the properties satisfying `P`
are those of a signature, it is that signature. -/
def ofProperties (P : Property → Prop) [DecidablePred P] : Signature :=
  ([addMult, antiAddMult, additive, mult, antiAdd, antiMult, mono, anti].find?
    (fun σ ↦ ∀ p ∈ σ.properties, P p)).getD all

/-- In the refinement order ([icard-2012]'s ≼, §2.2), `σ ≤ τ` iff every σ-function is a τ-function,
i.e. iff the properties of `τ` are among those of `σ` (`Signature.SoundFor.of_le` in
`Logic/Natural/Soundness.lean`). The most specific signature, which [icard-2012] calls
≼-maximal, is the least one in this order. -/
instance : PartialOrder Signature :=
  .lift (fun σ ↦ OrderDual.toDual (properties σ))
    (OrderDual.toDual.injective.comp properties_injective)

theorem le_iff {σ τ : Signature} :
    σ ≤ τ ↔ properties τ ⊆ properties σ := Iff.rfl

instance : DecidableLE Signature := fun _ _ ↦
  decidable_of_iff _ le_iff.symm

instance : OrderTop Signature where
  top := .all
  le_top _ := le_iff.mpr (Finset.empty_subset _)

/-- The property a function with property `p` after one with property `q` has for that pair, when
there is one (`Signature.Property.HoldsFor.compose` in `Logic/Natural/Soundness.lean`). -/
def Property.compose : Property → Property → Option Property
  | .monotone, .monotone | .antitone, .antitone => some .monotone
  | .monotone, .antitone | .antitone, .monotone => some .antitone
  | .additive, .additive | .antiMultiplicative, .antiAdditive => some .additive
  | .multiplicative, .multiplicative | .antiAdditive, .antiMultiplicative => some .multiplicative
  | .antiAdditive, .additive | .multiplicative, .antiAdditive => some .antiAdditive
  | .antiMultiplicative, .multiplicative | .additive, .antiMultiplicative =>
      some .antiMultiplicative
  | _, _ => none

private theorem Property.compose_assoc : ∀ p q r : Property,
    (p.compose q).bind (·.compose r) = (q.compose r).bind (p.compose ·) := by
  decide

/-! ### Composition -/

/-- The composition `compose ψ φ` of projectivity signatures ([icard-2012], Definition 2.6 and
Lemma 2.7), `φ` inner and `ψ` outer, is the signature asserting what the property rule gives for
each property of `ψ` and of `φ` (`Signature.mem_properties_mul`). A ψ-function after a
φ-function is a `ψ * φ`-function (`Signature.HoldsFor.comp`), and no more specific signature holds
of all such composites (`Signature.isLeast_compose`). Three cells of the printed table (p. 716)
differ, at `antiAdd * antiAdd`, `antiMult * mult` and `antiAddMult * antiMult`. -/
def compose (ψ φ : Signature) : Signature :=
  ofProperties fun r ↦ ∃ p ∈ ψ.properties, ∃ q ∈ φ.properties, p.compose q = some r

instance : Mul Signature where mul := compose
instance : One Signature where one := .addMult

theorem mem_properties_mul {ψ φ : Signature} {r : Property} :
    r ∈ (ψ * φ).properties ↔ ∃ p ∈ ψ.properties, ∃ q ∈ φ.properties, p.compose q = some r := by
  revert ψ φ r
  decide

/-- The signatures form a monoid under composition with identity the morphism signature `⊕`
([icard-2012] Lemma 2.7), associative because the property rule is. It is not commutative, since
`antiMult * antiAdd = additive` but `antiAdd * antiMult = mult` (p. 716). -/
instance : Monoid Signature where
  mul_assoc ψ φ χ := properties_injective <| Finset.ext fun _ ↦ by
    simp only [mem_properties_mul]
    exact exists_bind_comm Property.compose_assoc
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl

/-- `•` absorbs on the left ([icard-2012] p. 716). -/
@[simp] theorem top_mul (σ : Signature) : ⊤ * σ = ⊤ := by cases σ <;> rfl

/-- `•` absorbs on the right ([icard-2012] p. 716). -/
@[simp] theorem mul_top (σ : Signature) : σ * ⊤ = ⊤ := by cases σ <;> rfl

/-! ### Signs and polarities -/

/-- The sign of a signature is its marking in the Monotonicity Calculus: `1` if its class is
monotone, `-1` if it is antitone, and `0` otherwise, as for a non-monotone context such as
*exactly n* or an arbitrary one. -/
def sign (φ : Signature) : SignType :=
  if .monotone ∈ φ.properties then 1 else if .antitone ∈ φ.properties then -1 else 0

theorem sign_eq_one_iff {φ : Signature} : φ.sign = 1 ↔ .monotone ∈ φ.properties := by
  revert φ; decide

theorem sign_eq_neg_one_iff {φ : Signature} : φ.sign = -1 ↔ .antitone ∈ φ.properties := by
  revert φ; decide

theorem sign_mul (φ ψ : Signature) : (φ * ψ).sign = φ.sign * ψ.sign := by
  revert φ ψ; decide

/-- `sign` as a monoid homomorphism: the projectivity calculus composes its markings as the
Monotonicity Calculus composes `+` and `−` ([icard-2012] p. 716). -/
def signHom : Signature →* SignType where
  toFun := sign
  map_one' := by decide
  map_mul' := sign_mul

/-- A polarity as a signature, the positive one the morphism signature `⊕` and the negative one
the anti-morphism `⊖`. -/
def ofPolarity : Polarity →* Signature := Polarity.lift ⟨.antiAddMult, rfl⟩

@[simp] theorem sign_ofPolarity (p : Polarity) : (ofPolarity p).sign = p := by
  cases p <;> decide

/-- Only `⊕` and `⊖` are invertible, each its own inverse ([icard-2012] p. 716), so the invertible
signatures are the two polarities. -/
theorem isUnit_iff {σ : Signature} : IsUnit σ ↔ σ ∈ Set.range ofPolarity := by
  rw [isUnit_iff_exists, Set.mem_range]
  revert σ
  decide

end Signature

/-! ### The function class of a signature -/

section HoldsFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]

/-- The function class a property asserts. -/
def Signature.Property.HoldsFor : Signature.Property → (α → β) → Prop
  | .monotone => Monotone
  | .antitone => Antitone
  | .additive => fun f => (∀ p q, f (p ⊔ q) = f p ⊔ f q) ∧ f ⊤ = ⊤
  | .multiplicative => fun f => (∀ p q, f (p ⊓ q) = f p ⊓ f q) ∧ f ⊥ = ⊥
  | .antiAdditive => fun f => IsAntiAdditive f ∧ f ⊤ = ⊥
  | .antiMultiplicative => fun f => IsAntiMultiplicative f ∧ f ⊥ = ⊤

/-- A function has signature σ — is a "σ-function" — when it has every
property σ asserts. -/
def Signature.HoldsFor (σ : Signature) (f : α → β) : Prop :=
  ∀ p ∈ σ.properties, p.HoldsFor f

theorem Signature.HoldsFor.of_le {σ τ : Signature} {f : α → β}
    (h : σ.HoldsFor f) (hστ : σ ≤ τ) : τ.HoldsFor f :=
  fun p hp ↦ h p (Signature.le_iff.mp hστ hp)

theorem Signature.holdsFor_mono_iff {f : α → β} : Signature.HoldsFor .mono f ↔ Monotone f := by
  simp [Signature.HoldsFor, Signature.properties, Signature.Property.HoldsFor]

theorem Signature.holdsFor_anti_iff {f : α → β} : Signature.HoldsFor .anti f ↔ Antitone f := by
  simp [Signature.HoldsFor, Signature.properties, Signature.Property.HoldsFor]

theorem Signature.holdsFor_antiAdd_iff {f : α → β} :
    Signature.HoldsFor .antiAdd f ↔ IsAntiAdditive f ∧ f ⊤ = ⊥ := by
  simp only [Signature.HoldsFor, Signature.properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Signature.Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.antitone, h⟩⟩

theorem Signature.holdsFor_antiAddMult_iff {f : α → β} :
    Signature.HoldsFor .antiAddMult f ↔
      (IsAntiAdditive f ∧ f ⊤ = ⊥) ∧ IsAntiMultiplicative f ∧ f ⊥ = ⊤ := by
  simp only [Signature.HoldsFor, Signature.properties, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Signature.Property.HoldsFor]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.1.antitone, h⟩⟩

theorem Signature.holdsFor_addMult_of_galoisConnection {f u l : α → α}
    (gc₁ : GaloisConnection f u) (gc₂ : GaloisConnection l f) :
    Signature.HoldsFor .addMult f := by
  intro p hp
  cases p with
  | monotone => exact gc₁.monotone_l
  | additive => exact ⟨fun _ _ ↦ gc₁.l_sup, gc₂.u_top⟩
  | multiplicative => exact ⟨fun _ _ ↦ gc₂.u_inf, gc₁.l_bot⟩
  | antitone | antiAdditive | antiMultiplicative => exact absurd hp (by decide)

theorem Signature.holdsFor_addMult_id : Signature.HoldsFor .addMult (id : α → α) :=
  Signature.holdsFor_addMult_of_galoisConnection GaloisConnection.id GaloisConnection.id

theorem Signature.holdsFor_antiAddMult_compl {γ : Type*} [BooleanAlgebra γ] :
    Signature.HoldsFor .antiAddMult (compl : γ → γ) := by
  intro p hp
  cases p with
  | antitone => exact compl_anti
  | antiAdditive => exact ⟨isAntiAdditive_compl, compl_top⟩
  | antiMultiplicative => exact ⟨isAntiMultiplicative_compl, compl_bot⟩
  | monotone | additive | multiplicative => exact absurd hp (by decide)

/-- The property rule for composition is sound: a function with property `p` after one with
property `q` has the property `Signature.Property.compose` says. -/
theorem Signature.Property.HoldsFor.compose {γ : Type*} [Lattice γ] [BoundedOrder γ]
    {p q r : Signature.Property} {f : β → γ} {g : α → β} (h : p.compose q = some r)
    (hf : p.HoldsFor f) (hg : q.HoldsFor g) : r.HoldsFor (f ∘ g) := by
  cases p <;> cases q <;> simp only [Signature.Property.compose, reduceCtorEq,
    Option.some.injEq] at h <;> subst h <;>
    simp only [Signature.Property.HoldsFor, IsAntiAdditive, IsAntiMultiplicative] at hf hg ⊢
  all_goals first
    | exact Monotone.comp hf hg
    | exact Antitone.comp hf hg
    | exact Monotone.comp_antitone hf hg
    | exact Antitone.comp_monotone hf hg
    | exact ⟨fun x y ↦ by simp only [Function.comp_apply, hg.1, hf.1],
        by simp only [Function.comp_apply, hg.2, hf.2]⟩

/-- A ψ-function after a φ-function is a `ψ * φ`-function, over any bounded lattices: the function
classes compose as `Signature.compose` says ([icard-2012] Definition 2.6 and Lemma 2.7). -/
theorem Signature.HoldsFor.comp {γ : Type*} [Lattice γ] [BoundedOrder γ] {ψ φ : Signature}
    {f : β → γ} {g : α → β} (hf : ψ.HoldsFor f) (hg : φ.HoldsFor g) :
    (ψ * φ).HoldsFor (f ∘ g) := fun _ hr ↦ by
  obtain ⟨p, hp, q, hq, h⟩ := Signature.mem_properties_mul.1 hr
  exact (hf p hp).compose h (hg q hq)

/-- A function in the class of a signature of positive sign is monotone. -/
theorem Signature.HoldsFor.monotone_of_sign_eq_one {σ : Signature} {f : α → β}
    (h : σ.HoldsFor f) (hs : σ.sign = 1) : Monotone f :=
  h _ (Signature.sign_eq_one_iff.1 hs)

/-- A function in the class of a signature of negative sign is antitone. -/
theorem Signature.HoldsFor.antitone_of_sign_eq_neg_one {σ : Signature} {f : α → β}
    (h : σ.HoldsFor f) (hs : σ.sign = -1) : Antitone f :=
  h _ (Signature.sign_eq_neg_one_iff.1 hs)

end HoldsFor

section DecidableHoldsFor

variable {α β : Type*} [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]
  [Fintype α] [DecidableLE α] [DecidableEq β] [DecidableLE β]

instance Signature.Property.decidableHoldsFor :
    ∀ (p : Signature.Property) (f : α → β), Decidable (p.HoldsFor f)
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

instance Signature.decidableHoldsFor (σ : Signature) (f : α → β) :
    Decidable (σ.HoldsFor f) :=
  inferInstanceAs (Decidable (∀ p ∈ σ.properties, p.HoldsFor f))

end DecidableHoldsFor

end NaturalLogic
