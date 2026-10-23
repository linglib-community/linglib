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
the nine entailment signatures of [icard-2012], with the operations of the projectivity calculus:
chaining two relations, projecting a relation through a function of known signature, and composing
signatures. A relation is a conjunction of atomic constraints, so `≡` also satisfies `⊑`; the
mutually exclusive relations of [maccartney-manning-2009] are their strict versions.

## Main declarations

* `Relation`: the seven relations, a monoid under `Relation.join` with identity `equiv` and
  absorbing element `independent`.
* `Relation.constraints`: the atomic constraints a relation asserts; `R ≤ R'` iff `R` entails `R'`,
  iff the constraints of `R'` are among those of `R`. `#` is the top, and there is no bottom.
* `Signature`: the nine signatures, a monoid under `Signature.compose` with identity `addMult` and
  absorbing element `all`.
* `Signature.project`: projection of a relation through a signature, an action of the signature
  monoid on the relations (`MulAction Signature Relation`).
* `Signature.contextProjectivity`: the signature of a position, the product along its path.
* `Signature.sign`: whether a signature is upward or downward entailing, a monoid homomorphism
  (`Signature.signHom`); negation's sign is that of the negative `Polarity`.

## Implementation notes

`compose` is computed from `project` at the relations `forward` and `negation`, so
`projection_composition` holds by construction. Associativity of `join` is printed in neither
source and is checked by `decide`. The tables are proved sound in `Logic/Natural/Soundness.lean`
and optimal in `Logic/Natural/Completeness.lean`, which also shows that the seven relations are
the nondegenerately realizable constraint sets. Signatures are ordered by their property sets.

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

/-- The atomic constraints a relation asserts: `≡` is `{le, ge}`, `^` is `{disjoint, codisjoint}`
and `#` is `∅`. A relation holds iff all its constraints do (`Relation.holds_iff` in
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

/-- The implication order ([icard-2012]'s ≪): `R ≤ R'` iff `xRy` entails `xR'y`, i.e. iff the
constraints of `R'` are among those of `R` (`Relation.Holds.of_le`). It consists of two diamonds
sharing only the top `#`, one with `≡` below `⊑` and `⊒`, the other with `^` below `|` and `⌣`;
there is no bottom, since `x = y` makes `x` and `y` neither disjoint nor exhaustive. -/
instance : PartialOrder Relation :=
  .lift (fun R => OrderDual.toDual (constraints R))
    (OrderDual.toDual.injective.comp constraints_injective)

theorem le_iff {R R' : Relation} :
    R ≤ R' ↔ constraints R' ⊆ constraints R := Iff.rfl

instance : DecidableLE Relation := fun _ _ =>
  decidable_of_iff _ le_iff.symm

instance : OrderTop Relation where
  top := .independent
  le_top _ := le_iff.mpr (Finset.empty_subset _)

/--
The join `R ⋈ R'` ([icard-2012], Lemma 1.5): given `xRy` and `yR'z`, the strongest relation
guaranteed between `x` and `z`. This is relation-algebra join, not lattice join. Each cell is sound
(`Relation.Holds.join` in `Logic/Natural/Soundness.lean`) and is the least sound relation
(`Relation.isLeast_join` in `Logic/Natural/Completeness.lean`), as in [icard-2012]'s
Definition 1.4. [maccartney-manning-2009]'s §3 join is exact relation composition, which on 17 of
the 49 cells is a union of the seven relations; this table gives the best single relation there.
-/
def join : Relation → Relation → Relation
  -- ≡ is the identity
  | .equiv, r => r
  | r, .equiv => r
  -- ⊑ column
  | .forward, .forward => .forward
  | .forward, .reverse => .independent
  | .forward, .negation => .alternation
  | .forward, .alternation => .alternation
  | .forward, .cover => .independent
  | .forward, .independent => .independent
  -- ⊒ column
  | .reverse, .forward => .independent
  | .reverse, .reverse => .reverse
  | .reverse, .negation => .cover
  | .reverse, .alternation => .independent
  | .reverse, .cover => .cover
  | .reverse, .independent => .independent
  -- ^ column
  | .negation, .forward => .cover
  | .negation, .reverse => .alternation
  | .negation, .negation => .equiv
  | .negation, .alternation => .reverse
  | .negation, .cover => .forward
  | .negation, .independent => .independent
  -- | column
  | .alternation, .forward => .independent
  | .alternation, .reverse => .alternation
  | .alternation, .negation => .forward
  | .alternation, .alternation => .independent
  | .alternation, .cover => .forward
  | .alternation, .independent => .independent
  -- ⌣ column
  | .cover, .forward => .cover
  | .cover, .reverse => .independent
  | .cover, .negation => .reverse
  | .cover, .alternation => .reverse
  | .cover, .cover => .independent
  | .cover, .independent => .independent
  -- # column
  | .independent, _ => .independent

instance : Mul Relation := ⟨join⟩
instance : One Relation := ⟨.equiv⟩

/-- The relations form a monoid under ⋈ with identity `≡`. The identity and absorption laws are
printed in [icard-2012] (p. 710); associativity appears in neither [icard-2012] nor
[maccartney-manning-2009] and is checked by `decide`. The monoid is not commutative:
`^ ⋈ ⌣ = ⊑` but `⌣ ⋈ ^ = ⊒`. -/
instance : Monoid Relation where
  mul_assoc := by decide
  one_mul r := by cases r <;> rfl
  mul_one r := by cases r <;> rfl

/-- `#` absorbs on the left ([icard-2012] p. 710). -/
@[simp] theorem top_mul (r : Relation) : ⊤ * r = ⊤ := by cases r <;> rfl

/-- `#` absorbs on the right ([icard-2012] p. 710). -/
@[simp] theorem mul_top (r : Relation) : r * ⊤ = ⊤ := by cases r <;> rfl

end Relation

/-! ### Entailment signatures -/

/-- The function classes a relation can be projected through, from
arbitrary (`•`) to anti-morphism (`◇⊟`). -/
inductive Signature where
  /-- An arbitrary function (`•`), projecting every relation to `#`. -/
  | all
  /-- A monotone function (`+`, upward entailing). -/
  | mono
  /-- An antitone function (`−`, downward entailing). -/
  | anti
  /-- An additive function (`⊕`), preserving joins. -/
  | additive
  /-- An anti-additive function (`◇`), turning joins into meets. -/
  | antiAdd
  /-- A multiplicative function (`⊞`), preserving meets. -/
  | mult
  /-- An anti-multiplicative function (`⊟`), turning meets into joins. -/
  | antiMult
  /-- A morphism (`⊕⊞`), additive and multiplicative. -/
  | addMult
  /-- An anti-morphism (`◇⊟`), anti-additive and anti-multiplicative. -/
  | antiAddMult
  deriving DecidableEq, Fintype, Repr

namespace Signature

/-- The function properties a signature can assert, closed under
implication (an additive function is monotone, so `⊕`'s set contains
`monotone`). -/
inductive Property where
  /-- Preserves `≤`. -/
  | monotone
  /-- Reverses `≤`. -/
  | antitone
  /-- Preserves `⊔`. -/
  | additive
  /-- Preserves `⊓`. -/
  | multiplicative
  /-- Sends `⊔` to `⊓`. -/
  | antiAdditive
  /-- Sends `⊓` to `⊔`. -/
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

/-- The refinement order ([icard-2012]'s ≼, §2.2): `σ ≤ τ` iff every σ-function is a τ-function,
i.e. iff the properties of `τ` are among those of `σ` (`Signature.SoundFor.of_le` in
`Logic/Natural/Soundness.lean`). -/
instance : PartialOrder Signature :=
  .lift (fun σ => OrderDual.toDual (properties σ))
    (OrderDual.toDual.injective.comp properties_injective)

theorem le_iff {σ τ : Signature} :
    σ ≤ τ ↔ properties τ ⊆ properties σ := Iff.rfl

instance : DecidableLE Signature := fun _ _ =>
  decidable_of_iff _ le_iff.symm

instance : OrderTop Signature where
  top := .all
  le_top _ := le_iff.mpr (Finset.empty_subset _)

/-- The projection of a relation through a function of the given signature: the strongest
relation guaranteed between `f x` and `f y` when `x R y` and `f` has signature `σ` ([icard-2012]
Definition 2.3, computed by his Lemma 2.4). Each row is sound (`soundFor_*` in
`Logic/Natural/Soundness.lean`) and least (`Signature.isLeast_project` in
`Logic/Natural/Completeness.lean`). One cell departs from the printed table: [icard-2012] prints
`[R]^• = #` for all `R` (p. 715), but every function preserves equality, so his Definition 2.3
forces `[≡]^• = ≡`. -/
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

theorem project_equiv (φ : Signature) : project .equiv φ = .equiv := by
  cases φ <;> rfl

theorem project_independent (φ : Signature) : project .independent φ = .independent := by
  cases φ <;> rfl

/--
The signature whose projections of `forward` and `negation` are the given relations. These two
projections identify each signature; for `•` both are `#`.
-/
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

/--
Composition of entailment signatures ([icard-2012], Lemma 2.7): `compose ψ φ` is the unique
signature whose projection table is that of projecting through `φ` and then `ψ`. It is computed
from the projections of `forward` and `negation`, which distinguish all 9 signatures; for `•` both
are `#`, which makes it absorbing ([icard-2012] p. 716).
-/
def compose (ψ φ : Signature) : Signature :=
  fromProjectionPair
    (project (project .forward φ) ψ)
    (project (project .negation φ) ψ)

/-- `addMult` (⊕⊞, the morphism class) is the identity for composition
([icard-2012] Lemma 2.7). -/
theorem compose_identity_left (s : Signature) : compose .addMult s = s := by
  cases s <;> rfl

theorem compose_identity_right (s : Signature) : compose s .addMult = s := by
  cases s <;> rfl

/-- `•` is absorbing: `φ ∘ • = • = • ∘ φ` ([icard-2012] p. 716). -/
theorem compose_all_left (s : Signature) : compose .all s = .all := by
  cases s <;> rfl

theorem compose_all_right (s : Signature) : compose s .all = .all := by
  cases s <;> rfl

theorem compose_assoc (a b c : Signature) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a <;> cases b <;> cases c <;> rfl

-- Monoid instance (compose with identity `addMult`)
instance : Mul Signature where mul := compose
instance : One Signature where one := .addMult
instance : Monoid Signature where
  mul_assoc a b c := compose_assoc a b c
  one_mul := compose_identity_left
  mul_one := compose_identity_right

end Signature

/-! ### The sign of a signature -/

namespace Signature

/-- The sign of a signature ([icard-2012]'s coarse upward/downward distinction): `1` if it
preserves forward entailment (`[⊑]^φ = ⊑`), `-1` if it reverses it (`[⊑]^φ = ⊒`), and `0`
otherwise, as for a non-monotone context such as *exactly n* or an arbitrary one. -/
def sign (φ : Signature) : SignType :=
  if project .forward φ == .forward then 1
  else if project .forward φ == .reverse then -1
  else 0

theorem sign_mul (φ ψ : Signature) : (φ * ψ).sign = φ.sign * ψ.sign := by
  cases φ <;> cases ψ <;> rfl

/-- `sign` as a monoid homomorphism. -/
def signHom : Signature →* SignType where
  toFun := sign
  map_one' := rfl
  map_mul' := sign_mul

theorem sign_antiAddMult : antiAddMult.sign = (Polarity.negative : SignType) := rfl

/-- The projectivity signature of a position: the product of the signatures along its path,
outermost first ([icard-2012]'s `pro(s(u)) = top(s) ∘ pro(u)`, Definition 2.9). Under the
projection action the innermost (last) signature applies first. For example,
`contextProjectivity [.antiAdd, .addMult] = .antiAdd`: an intersective modifier inside the
restrictor of *no* leaves the position anti-additive. -/
def contextProjectivity (path : List Signature) : Signature :=
  path.prod

end Signature

/-! ### Projection composition -/

/-- Projecting through `φ` and then `ψ` is projecting through `compose ψ φ` ([icard-2012]
Definition 2.6 and Lemma 2.7). Since `compose` is computed from the projections of `forward` and
`negation`, this says that these two projections determine the whole table. -/
theorem projection_composition (R : Relation) (φ ψ : Signature) :
    Signature.project (Signature.project R φ) ψ =
    Signature.project R (Signature.compose ψ φ) := by
  cases R <;> cases φ <;> cases ψ <;> rfl

instance : SMul Signature Relation := ⟨λ σ R => Signature.project R σ⟩

@[simp] theorem Signature.smul_def (σ : Signature) (R : Relation) :
    σ • R = Signature.project R σ := rfl

/-- Projection is an action of the signature monoid on the relations:
`projection_composition` is the `mul_smul` law. -/
instance : MulAction Signature Relation where
  one_smul := by decide
  mul_smul ψ φ R := (projection_composition R φ ψ).symm

/-! ### The negation signature -/

/-- Negation has the anti-morphism signature ◇⊟, the strongest downward-entailing signature. -/
def negationSignature : Signature := .antiAddMult

end NaturalLogic
