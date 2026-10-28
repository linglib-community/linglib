module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Basic.Sign.Defs
public import Linglib.Semantics.Polarity.Basic

/-!
# The natural-logic relation algebra

This file defines the seven natural-logic relations between denotations (≡, ⊑, ⊒, ^, |, ⌣, #) and
the nine projectivity signatures of [icard-2012], with the operations of his projectivity calculus:
chaining two relations, projecting a relation through a function of known signature, and composing
signatures. A relation is a conjunction of atomic constraints, so `≡` also satisfies `⊑`; the
mutually exclusive relations of [maccartney-manning-2009] are their strict versions.

Each operation is a rule on single atoms or properties lifted to the conjunctions. A constraint
between `x` and `y` followed by one between `y` and `z` gives at most one constraint between `x` and
`z` (`Relation.Atom.join`), a function with one property carries a constraint between its arguments
to at most one between its values (`Signature.Property.project`), and a function with one property
after a function with another has at most one property for that pair (`Signature.Property.compose`).
The tables of [icard-2012] are what these rules give, cell by cell, except that every function
carries `≡` to `≡`.

## Main declarations

* `Relation`: the seven relations, a monoid under `Relation.join` with identity `≡` and absorbing
  element `#`.
* `Relation.constraints`: the atomic constraints a relation asserts; `R ≤ R'` iff `R` entails `R'`,
  iff the constraints of `R'` are among those of `R`. `#` is the top, and there is no bottom.
* `Signature`: the nine signatures, a monoid under `Signature.compose` with identity `⊕` and
  absorbing element `•`, whose invertible elements are the two polarities
  (`Signature.isUnit_iff`).
* `Signature.project`: projection of a relation through a signature, a faithful action of the
  signature monoid on the relations.
* `Signature.sign`: the Monotonicity Calculus marking of a signature, upward, downward or neither,
  a monoid homomorphism (`Signature.signHom`).

## Implementation notes

The monoid laws and the action law follow from the rules: the atom and property rules are
associative, and the property rule for projection is compatible with the one for composition.
Each rule is proved sound in `Logic/Natural/Soundness.lean`, and the lifted operations are proved
optimal in `Logic/Natural/Completeness.lean`, which also shows that the seven relations are the
nondegenerately realizable constraint sets. Signatures are ordered by their property sets.

## References

* [icard-2012] — the projectivity calculus: the relations, signatures,
  and tables this file implements.
* [maccartney-manning-2009] — the extended natural-logic model; its §3
  join is exact relation composition, union-valued outside the seven.
-/

@[expose] public section

namespace NaturalLogic

/-- Chaining two partial operations gives the same results in either bracketing when the operations
agree pointwise. -/
private theorem exists_bind_comm {α β γ δ ζ ε : Type*} {f : α → β → Option γ}
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

/-! ### The seven relations -/

/-- The seven natural-logic relations between denotations. -/
inductive Relation where
  /-- Equivalence `≡` holds when the denotations coincide (*couch* / *sofa*). -/
  | equiv
  /-- Forward entailment `⊑` holds when `A ⊆ B` (*dog* / *animal*). -/
  | forward
  /-- Reverse entailment `⊒` holds when `A ⊇ B` (*animal* / *dog*). -/
  | reverse
  /-- Negation `^` holds when the denotations are disjoint and exhaustive
      (*happy* / *unhappy*). -/
  | negation
  /-- Alternation `|` holds when the denotations are disjoint (*cat* / *dog*). -/
  | alternation
  /-- Cover `⌣` holds when the denotations are exhaustive (*animal* / *nondog*). -/
  | cover
  /-- Independence `#` imposes no constraint (*hungry* / *tall*). -/
  | independent
  deriving DecidableEq, Fintype, Repr

namespace Relation

/-- The atomic lattice constraints a relation can impose
([icard-2012] Definition 1.2). -/
inductive Atom where
  /-- `x ≤ y`. -/
  | le
  /-- `y ≤ x`. -/
  | ge
  /-- `x ⊓ y = ⊥`. -/
  | disjoint
  /-- `x ⊔ y = ⊤`. -/
  | codisjoint
  deriving DecidableEq, Fintype, Repr

/-- The atomic constraints a relation asserts, `{le, ge}` for `≡`, `{disjoint, codisjoint}` for `^`
and `∅` for `#`. A relation holds iff all its constraints do (`Relation.holds_iff` in
`Logic/Natural/Soundness.lean`), and of the sixteen constraint sets exactly these seven are
nondegenerately realizable (`Relation.mem_range_constraints_iff` in
`Logic/Natural/Completeness.lean`). -/
def constraints : Relation → Finset Atom
  | .equiv => {.le, .ge}
  | .forward => {.le}
  | .reverse => {.ge}
  | .negation => {.disjoint, .codisjoint}
  | .alternation => {.disjoint}
  | .cover => {.codisjoint}
  | .independent => ∅

theorem constraints_injective : Function.Injective constraints := by decide

/-- The strongest relation all of whose constraints satisfy `P`, found by trying the relations
from the strongest down to `#`, which has none. When the atoms satisfying `P` are the constraints
of a relation, it is that relation. -/
def ofAtoms (P : Atom → Prop) [DecidablePred P] : Relation :=
  ([equiv, negation, forward, reverse, alternation, cover].find?
    (fun R ↦ ∀ a ∈ R.constraints, P a)).getD independent

/-- In the implication order ([icard-2012]'s ≪), `R ≤ R'` iff `xRy` entails `xR'y`, i.e. iff the
constraints of `R'` are among those of `R` (`Relation.Holds.of_le`). It consists of two diamonds
sharing only the top `#`, one with `≡` below `⊑` and `⊒`, the other with `^` below `|` and `⌣`;
there is no bottom, since `x = y` makes `x` and `y` neither disjoint nor exhaustive. The most
informative relation, which [icard-2012] calls ≪-maximal, is the least one in this order. -/
instance : PartialOrder Relation :=
  .lift (fun R ↦ OrderDual.toDual (constraints R))
    (OrderDual.toDual.injective.comp constraints_injective)

theorem le_iff {R R' : Relation} :
    R ≤ R' ↔ constraints R' ⊆ constraints R := Iff.rfl

instance : DecidableLE Relation := fun _ _ ↦
  decidable_of_iff _ le_iff.symm

instance : OrderTop Relation where
  top := .independent
  le_top _ := le_iff.mpr (Finset.empty_subset _)

/-- The constraint between `x` and `z` that a constraint between `x` and `y` and one between `y`
and `z` guarantee, when there is one (`Relation.Atom.Holds.join` in `Logic/Natural/Soundness.lean`):
`≤` and `≥` are transitive, disjointness is inherited downward and codisjointness upward, and,
in a distributive lattice, `x` disjoint from `y` and `y` codisjoint with `z` give `x ≤ z`. -/
def Atom.join : Atom → Atom → Option Atom
  | .le, .le => some .le
  | .ge, .ge => some .ge
  | .le, .disjoint => some .disjoint
  | .disjoint, .ge => some .disjoint
  | .ge, .codisjoint => some .codisjoint
  | .codisjoint, .le => some .codisjoint
  | .disjoint, .codisjoint => some .le
  | .codisjoint, .disjoint => some .ge
  | _, _ => none

private theorem Atom.join_assoc :
    ∀ a b c : Atom, (a.join b).bind (·.join c) = (b.join c).bind (a.join ·) := by
  decide

/-- The join `R ⋈ R'` ([icard-2012], Lemma 1.5) is the strongest relation guaranteed between `x`
and `z` given `xRy` and `yR'z`, the relation asserting what the atom rule gives for each pair of
constraints of `R` and `R'` (`Relation.mem_constraints_mul`). It approximates relational
composition, which [maccartney-manning-2009] call join after the database operation; it is not the
lattice join.
Each cell is sound (`Relation.Holds.join` in `Logic/Natural/Soundness.lean`) and is the least
sound relation (`Relation.isLeast_join` in `Logic/Natural/Completeness.lean`), as [icard-2012]'s
Definition 1.4 requires. Exact composition is a union of the seven relations on 17 of the 49 cells
([maccartney-manning-2009] §3), and this gives the best single relation there. -/
def join (R S : Relation) : Relation :=
  ofAtoms fun c ↦ ∃ a ∈ R.constraints, ∃ b ∈ S.constraints, a.join b = some c

instance : Mul Relation := ⟨join⟩
instance : One Relation := ⟨.equiv⟩

theorem mem_constraints_mul {R S : Relation} {c : Atom} :
    c ∈ (R * S).constraints ↔ ∃ a ∈ R.constraints, ∃ b ∈ S.constraints, a.join b = some c := by
  revert R S c
  decide

/-- The relations form a monoid under ⋈ with identity `≡`. The identity and absorption laws are
printed in [icard-2012] (p. 710); associativity, printed in neither [icard-2012] nor
[maccartney-manning-2009], is that of the atom rule. The monoid is not commutative, since `^ ⋈ ⌣ =
⊑` but `⌣ ⋈ ^ = ⊒`. -/
instance : Monoid Relation where
  mul_assoc R S T := constraints_injective <| Finset.ext fun _ ↦ by
    simp only [mem_constraints_mul]
    exact exists_bind_comm Atom.join_assoc
  one_mul r := by cases r <;> rfl
  mul_one r := by cases r <;> rfl

/-- `#` absorbs on the left ([icard-2012] p. 710). -/
@[simp] theorem top_mul (r : Relation) : ⊤ * r = ⊤ := by cases r <;> rfl

/-- `#` absorbs on the right ([icard-2012] p. 710). -/
@[simp] theorem mul_top (r : Relation) : r * ⊤ = ⊤ := by cases r <;> rfl

end Relation

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

/-- The constraint between the values of a function with property `p` that a constraint `a`
between its arguments guarantees, when there is one (`Signature.Property.HoldsFor.project` in
`Logic/Natural/Soundness.lean`): a monotone function keeps `≤` and `≥` and an antitone one swaps
them, an additive function keeps codisjointness and a multiplicative one disjointness, an
anti-additive function turns codisjointness into disjointness and an anti-multiplicative one the
reverse. -/
def Property.project : Relation.Atom → Property → Option Relation.Atom
  | .le, .monotone => some .le
  | .ge, .monotone => some .ge
  | .le, .antitone => some .ge
  | .ge, .antitone => some .le
  | .codisjoint, .additive => some .codisjoint
  | .disjoint, .multiplicative => some .disjoint
  | .codisjoint, .antiAdditive => some .disjoint
  | .disjoint, .antiMultiplicative => some .codisjoint
  | _, _ => none

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

private theorem Property.compose_project : ∀ (p q : Property) (a : Relation.Atom),
    (p.compose q).bind (Property.project a ·) =
      (Property.project a q).bind (Property.project · p) := by
  decide

/-- The projection of a relation through a function of the given signature is the strongest relation
guaranteed between `f x` and `f y` when `x R y` and `f` has signature `σ` ([icard-2012] Definition
2.3, computed by his Lemma 2.4): `≡`, since every function preserves equality, and otherwise the
relation asserting what the property rule gives for each property of `σ` and constraint of `R`
(`Signature.mem_constraints_project`). Each row is sound (`Signature.soundFor_of_holdsFor` in
`Logic/Natural/Soundness.lean`) and least (`Signature.isLeast_project` in
`Logic/Natural/Completeness.lean`). [icard-2012] remarks under the table that `[R]^• = #` for all
`R` (p. 715), which is what the property rule alone gives for `≡` too. -/
def project (R : Relation) (σ : Signature) : Relation :=
  if R = .equiv then .equiv else
    Relation.ofAtoms fun b ↦ ∃ p ∈ σ.properties, ∃ a ∈ R.constraints, Property.project a p = some b

@[simp] theorem project_equiv (φ : Signature) : project .equiv φ = .equiv := rfl

@[simp] theorem project_independent (φ : Signature) : project .independent φ = .independent := by
  cases φ <;> rfl

theorem mem_constraints_project {R : Relation} (hR : R ≠ .equiv) {σ : Signature}
    {b : Relation.Atom} : b ∈ (project R σ).constraints ↔
      ∃ p ∈ σ.properties, ∃ a ∈ R.constraints, Property.project a p = some b := by
  revert R σ b
  decide

/-- Projection through a less specific signature gives a weaker relation. -/
theorem project_mono (R : Relation) : Monotone (project R) := by
  intro σ τ h
  by_cases hR : R = .equiv
  · subst hR
    exact le_rfl
  refine Relation.le_iff.2 fun _ hb ↦ ?_
  obtain ⟨p, hp, a, ha, hab⟩ := (mem_constraints_project hR).1 hb
  exact (mem_constraints_project hR).2 ⟨p, le_iff.1 h hp, a, ha, hab⟩

private theorem project_ne_equiv : ∀ {R : Relation} (σ : Signature), R ≠ .equiv →
    project R σ ≠ .equiv := by
  decide

/-! ### Composition -/

/-- The composition `compose ψ φ` of projectivity signatures ([icard-2012], Definition 2.6 and
Lemma 2.7), `φ` inner and `ψ` outer, is the signature asserting what the property rule gives for
each property of `ψ` and of `φ` (`Signature.mem_properties_mul`). A ψ-function after a
φ-function is a `ψ * φ`-function (`Signature.HoldsFor.comp`), and no more specific signature holds
of all such composites (`Signature.isLeast_compose`). Three cells of the printed table (p. 716) differ, at
`antiAdd * antiAdd`, `antiMult * mult` and `antiAddMult * antiMult`. -/
def compose (ψ φ : Signature) : Signature :=
  ofProperties fun r ↦ ∃ p ∈ ψ.properties, ∃ q ∈ φ.properties, p.compose q = some r

instance : Mul Signature where mul := compose
instance : One Signature where one := .addMult

theorem mem_properties_mul {ψ φ : Signature} {r : Property} :
    r ∈ (ψ * φ).properties ↔ ∃ p ∈ ψ.properties, ∃ q ∈ φ.properties, p.compose q = some r := by
  revert ψ φ r
  decide

/-- Projecting through `φ` and then through `ψ` is projecting through `ψ * φ` ([icard-2012]
Definition 2.6 and Lemma 2.7), since applying the composite property rule is applying the two
rules in turn. -/
theorem project_project (R : Relation) (φ ψ : Signature) :
    project (project R φ) ψ = project R (ψ * φ) := by
  by_cases hR : R = .equiv
  · subst hR; simp only [project_equiv]
  refine Relation.constraints_injective <| Finset.ext fun _ ↦ ?_
  simp only [mem_constraints_project (project_ne_equiv φ hR), mem_constraints_project hR,
    mem_properties_mul]
  exact (exists_bind_comm Property.compose_project).symm

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

instance : SMul Signature Relation := ⟨fun σ R ↦ project R σ⟩

@[simp] theorem smul_def (σ : Signature) (R : Relation) : σ • R = project R σ := rfl

/-- Projection is an action of the signature monoid on the relations, with
`Signature.project_project` as its `mul_smul` law. -/
instance : MulAction Signature Relation where
  one_smul := by decide
  mul_smul ψ φ R := (project_project R φ ψ).symm

private theorem eq_of_project_eq : ∀ σ τ : Signature, project .forward σ = project .forward τ →
    project .negation σ = project .negation τ → σ = τ := by
  decide

/-- A signature is determined by how it projects the relations, already by its projections of `⊑`
and `^`. -/
instance : FaithfulSMul Signature Relation where
  eq_of_smul_eq_smul {σ τ} h := eq_of_project_eq σ τ (h .forward) (h .negation)

/-! ### Signs and polarities -/

/-- The sign of a signature is its marking in the Monotonicity Calculus: `1` if it preserves forward
entailment (`[⊑]^φ = ⊑`), `-1` if it reverses it (`[⊑]^φ = ⊒`), and `0` otherwise, as for a
non-monotone context such as *exactly n* or an arbitrary one. -/
def sign (φ : Signature) : SignType :=
  if project .forward φ = .forward then 1
  else if project .forward φ = .reverse then -1
  else 0

theorem sign_mul (φ ψ : Signature) : (φ * ψ).sign = φ.sign * ψ.sign := by
  cases φ <;> cases ψ <;> rfl

/-- `sign` as a monoid homomorphism: the projectivity calculus composes its markings as the
Monotonicity Calculus composes `+` and `−` ([icard-2012] p. 716). -/
def signHom : Signature →* SignType where
  toFun := sign
  map_one' := rfl
  map_mul' := sign_mul

/-- A polarity as a signature, the positive one the morphism signature `⊕` and the negative one
the anti-morphism `⊖`. -/
def ofPolarity : Polarity →* Signature where
  toFun
    | .positive => .addMult
    | .negative => .antiAddMult
  map_one' := rfl
  map_mul' := by decide

@[simp] theorem sign_ofPolarity (p : Polarity) : (ofPolarity p).sign = p := by
  cases p <;> rfl

/-- Only `⊕` and `⊖` are invertible, each its own inverse ([icard-2012] p. 716), so the invertible
signatures are the two polarities. -/
theorem isUnit_iff {σ : Signature} : IsUnit σ ↔ σ ∈ Set.range ofPolarity := by
  rw [isUnit_iff_exists, Set.mem_range]
  revert σ
  decide

end Signature

end NaturalLogic
