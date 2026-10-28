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

`compose` is read off the projections of `⊑` and `^`, which determine a signature, and projecting
twice is projecting once through the composite (`Signature.project_project`), checked cell by
cell. Associativity of `join` is printed in neither source and is checked by `decide`. The tables
are proved sound in `Logic/Natural/Soundness.lean` and optimal in `Logic/Natural/Completeness.lean`,
which also shows that the seven relations are the nondegenerately realizable constraint sets.
Signatures are ordered by their property sets. Where [icard-2012]'s printed tables disagree with
his definitions, the definitions decide.

## References

* [icard-2012] — the projectivity calculus: the relations, signatures,
  and tables this file implements.
* [maccartney-manning-2009] — the extended natural-logic model; its §3
  join is exact relation composition, union-valued outside the seven.
-/

@[expose] public section

namespace NaturalLogic

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

/-- The join `R ⋈ R'` ([icard-2012], Lemma 1.5) is the strongest relation guaranteed between `x`
and `z` given `xRy` and `yR'z`. It approximates relational composition, which
[maccartney-manning-2009] call join after the database operation; it is not the lattice join.
Each cell is sound (`Relation.Holds.join` in `Logic/Natural/Soundness.lean`) and is the least
sound relation (`Relation.isLeast_join` in `Logic/Natural/Completeness.lean`), as [icard-2012]'s
Definition 1.4 requires. Exact composition is a union of the seven relations on 17 of the 49 cells
([maccartney-manning-2009] §3), and this table gives the best single relation there. -/
def join : Relation → Relation → Relation
  -- ≡ is the identity
  | .equiv, r => r
  | r, .equiv => r
  -- ⊑ row
  | .forward, .forward => .forward
  | .forward, .reverse => .independent
  | .forward, .negation => .alternation
  | .forward, .alternation => .alternation
  | .forward, .cover => .independent
  | .forward, .independent => .independent
  -- ⊒ row
  | .reverse, .forward => .independent
  | .reverse, .reverse => .reverse
  | .reverse, .negation => .cover
  | .reverse, .alternation => .independent
  | .reverse, .cover => .cover
  | .reverse, .independent => .independent
  -- ^ row
  | .negation, .forward => .cover
  | .negation, .reverse => .alternation
  | .negation, .negation => .equiv
  | .negation, .alternation => .reverse
  | .negation, .cover => .forward
  | .negation, .independent => .independent
  -- | row
  | .alternation, .forward => .independent
  | .alternation, .reverse => .alternation
  | .alternation, .negation => .forward
  | .alternation, .alternation => .independent
  | .alternation, .cover => .forward
  | .alternation, .independent => .independent
  -- ⌣ row
  | .cover, .forward => .cover
  | .cover, .reverse => .independent
  | .cover, .negation => .reverse
  | .cover, .alternation => .reverse
  | .cover, .cover => .independent
  | .cover, .independent => .independent
  -- # row
  | .independent, _ => .independent

instance : Mul Relation := ⟨join⟩
instance : One Relation := ⟨.equiv⟩

/-- The relations form a monoid under ⋈ with identity `≡`. The identity and absorption laws are
printed in [icard-2012] (p. 710); associativity appears in neither [icard-2012] nor
[maccartney-manning-2009] and is checked by `decide`. The monoid is not commutative, since `^ ⋈ ⌣ =
⊑` but `⌣ ⋈ ^ = ⊒`. -/
instance : Monoid Relation where
  mul_assoc := by decide
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

/-- The projection of a relation through a function of the given signature is the strongest relation
guaranteed between `f x` and `f y` when `x R y` and `f` has signature `σ` ([icard-2012] Definition
2.3, computed by his Lemma 2.4). Each row is sound (`soundFor_*` in `Logic/Natural/Soundness.lean`)
and least (`Signature.isLeast_project` in `Logic/Natural/Completeness.lean`). [icard-2012] remarks
under the table that `[R]^• = #` for all `R` (p. 715), but every function preserves equality, so
his Definition 2.3 forces `[≡]^• = ≡`. -/
def project : Relation → Signature → Relation
  | .equiv, .all => .equiv
  | _, .all => .independent
  | r, .addMult => r
  | .equiv, .antiAddMult => .equiv
  | .forward, .antiAddMult => .reverse
  | .reverse, .antiAddMult => .forward
  | .negation, .antiAddMult => .negation
  | .alternation, .antiAddMult => .cover
  | .cover, .antiAddMult => .alternation
  | .independent, .antiAddMult => .independent
  | .equiv, .mono => .equiv
  | .forward, .mono => .forward
  | .reverse, .mono => .reverse
  | .negation, .mono => .independent
  | .alternation, .mono => .independent
  | .cover, .mono => .independent
  | .independent, .mono => .independent
  | .equiv, .anti => .equiv
  | .forward, .anti => .reverse
  | .reverse, .anti => .forward
  | .negation, .anti => .independent
  | .alternation, .anti => .independent
  | .cover, .anti => .independent
  | .independent, .anti => .independent
  | .equiv, .additive => .equiv
  | .forward, .additive => .forward
  | .reverse, .additive => .reverse
  | .negation, .additive => .cover
  | .alternation, .additive => .independent
  | .cover, .additive => .cover
  | .independent, .additive => .independent
  | .equiv, .antiAdd => .equiv
  | .forward, .antiAdd => .reverse
  | .reverse, .antiAdd => .forward
  | .negation, .antiAdd => .alternation
  | .alternation, .antiAdd => .independent
  | .cover, .antiAdd => .alternation
  | .independent, .antiAdd => .independent
  | .equiv, .mult => .equiv
  | .forward, .mult => .forward
  | .reverse, .mult => .reverse
  | .negation, .mult => .alternation
  | .alternation, .mult => .alternation
  | .cover, .mult => .independent
  | .independent, .mult => .independent
  | .equiv, .antiMult => .equiv
  | .forward, .antiMult => .reverse
  | .reverse, .antiMult => .forward
  | .negation, .antiMult => .cover
  | .alternation, .antiMult => .cover
  | .cover, .antiMult => .independent
  | .independent, .antiMult => .independent

@[simp] theorem project_equiv (φ : Signature) : project .equiv φ = .equiv := by
  cases φ <;> rfl

@[simp] theorem project_independent (φ : Signature) : project .independent φ = .independent := by
  cases φ <;> rfl

/-! ### Composition -/

/-- The signature whose projections of `forward` and `negation` are the given relations. These two
projections identify each signature (`Signature.fromProjectionPair_project`); for `•` both are
`#`. -/
def fromProjectionPair : Relation → Relation → Signature
  | .independent, .independent => .all
  | .forward, .independent => .mono
  | .forward, .cover       => .additive
  | .forward, .alternation => .mult
  | .forward, .negation    => .addMult
  | .reverse, .independent => .anti
  | .reverse, .alternation => .antiAdd
  | .reverse, .cover       => .antiMult
  | .reverse, .negation    => .antiAddMult
  | _, _ => .mono  -- unreachable for valid projection pairs

theorem fromProjectionPair_project (σ : Signature) :
    fromProjectionPair (project .forward σ) (project .negation σ) = σ := by
  cases σ <;> rfl

/-- The composition `compose ψ φ` of projectivity signatures ([icard-2012], Definition 2.6 and
Lemma 2.7), `φ` inner and `ψ` outer, is the signature whose projection table is that of projecting
through `φ` and then `ψ` (`Signature.project_project`). It is read off the projections of `forward`
and `negation`, which identify a signature. Three cells of the printed table (p. 716) differ from
Definition 2.6, at `antiAdd * antiAdd`, `antiMult * mult` and `antiAddMult * antiMult`, and this
function follows the definition: a ψ-function after a φ-function is a `ψ * φ`-function
(`Signature.HoldsFor.comp`), and no more specific signature holds of all such composites
(`Signature.isLeast_compose`). -/
def compose (ψ φ : Signature) : Signature :=
  fromProjectionPair
    (project (project .forward φ) ψ)
    (project (project .negation φ) ψ)

instance : Mul Signature where mul := compose
instance : One Signature where one := .addMult

/-- Projecting through `φ` and then through `ψ` is projecting through `ψ * φ` ([icard-2012]
Definition 2.6 and Lemma 2.7). -/
theorem project_project (R : Relation) (φ ψ : Signature) :
    project (project R φ) ψ = project R (ψ * φ) := by
  cases R <;> cases φ <;> cases ψ <;> rfl

/-- The signatures form a monoid under composition with identity the morphism signature `⊕`
([icard-2012] Lemma 2.7). It is not commutative, since `antiMult * antiAdd = additive` but
`antiAdd * antiMult = mult` (p. 716). -/
instance : Monoid Signature where
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
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

/-- A signature is determined by how it projects the relations, already by its projections of `⊑`
and `^`. -/
instance : FaithfulSMul Signature Relation where
  eq_of_smul_eq_smul {σ τ} h := by
    rw [← fromProjectionPair_project σ, ← fromProjectionPair_project τ]
    exact congrArg₂ fromProjectionPair (h .forward) (h .negation)

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
